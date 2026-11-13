#!/usr/bin/env python3

"""
Reconstruct two haplotype graph traversals from a reference GFA path
and a bcftools-query TSV containing CHROM, POS, ID, REF, ALT, AT, GT.

Core model:
  - Start from the reference path extracted from the GFA.
  - For each record:
      * If GT is phased, keep it.
      * If GT is unphased, randomly assign phase using a reproducible RNG seed.
      * For each haplotype, allele 0 means keep reference.
      * Allele N>0 means replace the AT[0] reference traversal interval
        with AT[N].
  - Reconstruct each haplotype in one pass from sorted, non-overlapping
    replacement intervals.

Expected TSV columns:
  CHROM POS ID REF ALT AT GT

Recommended bcftools query pattern:
  bcftools query -s SAMPLE \
    -f '%CHROM\\t%POS\\t%ID\\t%REF\\t%ALT\\t%INFO/AT[\\t%GT]\\n'
"""

from __future__ import print_function

import argparse
import collections
import random
import re
import sys


Replacement = collections.namedtuple(
    "Replacement",
    [
        "chrom",
        "pos",
        "var_id",
        "start",
        "end",
        "traversal",
        "allele_index",
        "gt",
        "phase_source",
    ],
)


NODE_RE = re.compile(r"([><])([^><\s,]+)")

def log(msg):
    sys.stderr.write(str(msg) + "\n")
    sys.stderr.flush()


def warn(msg):
    sys.stderr.write("WARNING: {0}\n".format(msg))
    sys.stderr.flush()


def die(msg):
    sys.stderr.write("ERROR: {0}\n".format(msg))
    sys.exit(1)


def oriented_node_id(tok):
    """Return node ID without leading orientation."""
    if not tok:
        return tok
    if tok[0] in (">", "<"):
        return tok[1:]
    if tok[-1] in ("+", "-"):
        return tok[:-1]
    return tok


def flip_orientation(tok):
    if tok[0] == ">":
        return "<" + tok[1:]
    if tok[0] == "<":
        return ">" + tok[1:]
    if tok[-1] == "+":
        return tok[:-1] + "-"
    if tok[-1] == "-":
        return tok[:-1] + "+"
    return tok


def parse_walk_string(s):
    """
    Parse a walk/traversal string like:
      >1>2<3
    into:
      [">1", ">2", "<3"]

    Also accepts comma-separated P-line-ish tokens:
      1+,2-,3+
    returning:
      [">1", "<2", ">3"]
    """
    s = s.strip()

    if not s or s == ".":
        return []

    # GFA W-line or vg-style traversal syntax.
    if s[0] in (">", "<"):
        toks = []
        for m in NODE_RE.finditer(s):
            orient, node = m.groups()
            toks.append(orient + node)
        return toks

    # GFA P-line syntax: segment+,segment-,...
    if "," in s:
        toks = []
        for raw in s.split(","):
            raw = raw.strip()
            if not raw:
                continue
            if raw[-1] == "+":
                toks.append(">" + raw[:-1])
            elif raw[-1] == "-":
                toks.append("<" + raw[:-1])
            elif raw[0] in (">", "<"):
                toks.append(raw)
            else:
                # Default to forward if orientation is absent.
                toks.append(">" + raw)
        return toks

    # Single bare node.
    return [">" + s]


def path_to_w_string(path):
    """Write path as >node<node>node..."""
    return "".join(path)


def path_to_p_string(path):
    """Write path as GFA P-line segment list: node+,node-,..."""
    out = []
    for tok in path:
        if tok[0] == ">":
            out.append(tok[1:] + "+")
        elif tok[0] == "<":
            out.append(tok[1:] + "-")
        else:
            out.append(tok + "+")
    return ",".join(out)


def load_gfa_path(gfa_path, path_name):
    """
    Extract one path from GFA.

    Supports:
      P path_name segment+,segment-,... overlaps
      W sample hap seqid start end >walk

    For W-lines, this accepts --path-name matching one of:
      sample
      seqid
      sample#hap#seqid
      sample#seqid
    """
    found = []

    with open(gfa_path, "r") as fh:
        for line in fh:
            if not line or line[0] == "#":
                continue

            parts = line.rstrip("\n").split("\t")
            if not parts:
                continue

            rec_type = parts[0]

            if rec_type == "P":
                if len(parts) < 3:
                    continue
                name = parts[1]
                if name == path_name:
                    found.append(("P", name, parse_walk_string(parts[2])))

            elif rec_type == "W":
                if len(parts) < 7:
                    continue

                sample = parts[1]
                hap = parts[2]
                seqid = parts[3]
                walk = parts[6]

                candidates = set([
                    sample,
                    seqid,
                    sample + "#" + hap + "#" + seqid,
                    sample + "#" + seqid,
                ])

                if path_name in candidates:
                    found.append(("W", sample + "#" + hap + "#" + seqid,
                                  parse_walk_string(walk)))

    if len(found) == 0:
        die("No GFA path matched --path-name '{0}'".format(path_name))

    if len(found) > 1:
        names = ", ".join([x[1] for x in found[:10]])
        die("Multiple GFA paths matched --path-name '{0}': {1}".format(
            path_name, names
        ))

    path = found[0][2]

    if not path:
        die("Matched GFA path is empty: {0}".format(found[0][1]))

    return path

def build_ref_index(ref_path):
    """
    Index reference path positions by first oriented node and by unoriented node ID.

    This keeps memory modest:
      exact[">123"] -> [positions]
      unoriented["123"] -> [positions]
    """
    exact = collections.defaultdict(list)
    unoriented = collections.defaultdict(list)
    ref_ids = []

    for i, tok in enumerate(ref_path):
        exact[tok].append(i)
        node_id = oriented_node_id(tok)
        unoriented[node_id].append(i)
        ref_ids.append(node_id)

    return {
        "exact": exact,
        "unoriented": unoriented,
        "ref_ids": ref_ids,
    }

def split_at_field(at):
    """
    Split INFO/AT into per-allele traversal strings.

    Assumes no commas inside traversal strings, which should be true for
    Number=R String AT values like:
      >a>b>c,>a>d>c
    """
    if at is None or at == "." or at == "":
        return []
    return at.split(",")

# SUPERCEDED
def find_subpath(ref_path, query_path, ignore_orientation=False):
    """
    Return all (start, end) inclusive positions where query_path occurs
    contiguously in ref_path.
    """
    if not query_path:
        return []

    if len(query_path) > len(ref_path):
        return []

    if ignore_orientation:
        ref_cmp = [oriented_node_id(x) for x in ref_path]
        query_cmp = [oriented_node_id(x) for x in query_path]
    else:
        ref_cmp = ref_path
        query_cmp = query_path

    matches = []
    qlen = len(query_cmp)

    # Simple O(n*m) search is fine for prototype. If this becomes slow,
    # replace with KMP or pre-index candidate starts by first node.
    for i in range(0, len(ref_cmp) - qlen + 1):
        if ref_cmp[i:i + qlen] == query_cmp:
            matches.append((i, i + qlen - 1))

    return matches

def find_subpath_indexed(ref_path, ref_index, query_path, ignore_orientation=False):
    """
    Find contiguous query_path in ref_path using candidate starts from first node.

    This changes the search from:
      scan entire chromosome for every query
    to:
      only test positions where the first node matches
    """
    if not query_path:
        return []

    qlen = len(query_path)
    if qlen > len(ref_path):
        return []

    if ignore_orientation:
        first = oriented_node_id(query_path[0])
        candidates = ref_index["unoriented"].get(first, [])
        query_cmp = [oriented_node_id(x) for x in query_path]
        ref_cmp = ref_index["ref_ids"]
    else:
        first = query_path[0]
        candidates = ref_index["exact"].get(first, [])
        query_cmp = query_path
        ref_cmp = ref_path

    matches = []

    for i in candidates:
        j = i + qlen
        if j > len(ref_path):
            continue
        if ref_cmp[i:j] == query_cmp:
            matches.append((i, j - 1))

    return matches

def parse_gt(gt):
    """
    Parse GT into allele tokens and separator.

    Returns:
      alleles, sep

    Examples:
      0|1 -> (["0", "1"], "|")
      1/2 -> (["1", "2"], "/")
      ./. -> ([".", "."], "/")
    """
    gt = gt.strip()

    if "|" in gt:
        return gt.split("|"), "|"

    if "/" in gt:
        return gt.split("/"), "/"

    return [gt], None


def random_phase_gt(gt, rng):
    """
    Convert unphased diploid GT to randomly phased GT.

    0/1 -> 0|1 or 1|0
    1/2 -> 1|2 or 2|1
    1/1 -> 1|1
    """
    alleles, sep = parse_gt(gt)

    if sep == "|":
        return gt, "shapeit"

    if sep != "/":
        return gt, "unusable"

    if len(alleles) != 2:
        return gt, "unusable"

    a, b = alleles

    if a == "." or b == ".":
        return gt, "missing"

    if rng.random() < 0.5:
        return a + "|" + b, "random"
    else:
        return b + "|" + a, "random"


def read_tsv_records(tsv_path, has_header):
    with open(tsv_path, "r") as fh:
        for line_no, line in enumerate(fh, 1):
            line = line.rstrip("\n")

            if not line:
                continue

            if line_no == 1 and has_header:
                continue

            fields = line.split("\t")

            if len(fields) < 7:
                warn("TSV line {0}: expected at least 7 columns, saw {1}; skipping".format(
                    line_no, len(fields)
                ))
                continue

            chrom, pos, var_id, ref, alt, at, gt = fields[:7]

            try:
                pos_int = int(pos)
            except ValueError:
                warn("TSV line {0}: POS is not an integer: {1}; skipping".format(
                    line_no, pos
                ))
                continue

            yield {
                "line_no": line_no,
                "chrom": chrom,
                "pos": pos_int,
                "id": var_id,
                "ref": ref,
                "alt": alt,
                "at": at,
                "gt": gt,
            }


def build_replacements(records, ref_path, ref_index, rng, args):
    hap1 = []
    hap2 = []
    counts = collections.Counter()

    for rec in records:
        if args.progress_every > 0 and counts["records_total"] % args.progress_every == 0:
            log("Processed {0} records; shapeit={1}, random={2}, hap1_repl={3}, hap2_repl={4}, at0_not_found={5}".format(
                counts["records_total"],
                counts["shapeit_phased"],
                counts["random_phased"],
                counts["hap1_replacements"],
                counts["hap2_replacements"],
                counts["at0_not_found"],
            ))
        counts["records_total"] += 1

        at_entries = split_at_field(rec["at"])
        if not at_entries:
            counts["missing_at"] += 1
            if args.strict:
                warn_record(rec, "missing INFO/AT; skipping")
            continue

        at_paths = [parse_walk_string(x) for x in at_entries]

        if len(at_paths[0]) == 0:
            counts["empty_at0"] += 1
            warn_record(rec, "AT[0] is empty; skipping")
            continue

        phased_gt, phase_source = random_phase_gt(rec["gt"], rng)

        if phase_source == "shapeit":
            counts["shapeit_phased"] += 1
        elif phase_source == "random":
            counts["random_phased"] += 1
        elif phase_source == "missing":
            counts["missing_gt"] += 1
            warn_record(rec, "missing GT allele; skipping")
            continue
        else:
            counts["unusable_gt"] += 1
            warn_record(rec, "unusable GT '{0}'; skipping".format(rec["gt"]))
            continue

        alleles, sep = parse_gt(phased_gt)

        if sep != "|" or len(alleles) != 2:
            counts["non_diploid_or_unphased_after_processing"] += 1
            warn_record(rec, "GT did not become diploid phased GT: {0}; skipping".format(
                phased_gt
            ))
            continue

        # Locate the reference interval using AT[0], preferably exact orientation.
        matches = find_subpath_indexed(ref_path, ref_index, at_paths[0], ignore_orientation=False)

        if len(matches) == 0 and args.ignore_ref_orientation:
            matches = find_subpath_indexed(ref_path, ref_index, at_paths[0], ignore_orientation=True)
            if len(matches) > 0:
                counts["at0_matched_ignoring_orientation"] += 1

        if len(matches) == 0:
            counts["at0_not_found"] += 1
            warn_record(rec, "AT[0] was not found as a contiguous reference subpath; skipping")
            continue

        if len(matches) > 1:
            counts["at0_ambiguous"] += 1
            warn_record(rec, "AT[0] matched reference path {0} times; skipping".format(
                len(matches)
            ))
            continue

        start, end = matches[0]

        # Optional extra check: alt/ref allele count versus AT count.
        alt_count = 0 if rec["alt"] in ("", ".") else len(rec["alt"].split(","))
        expected_at_count = alt_count + 1
        if expected_at_count != len(at_entries):
            counts["at_count_mismatch"] += 1
            warn_record(
                rec,
                "ALT count implies {0} AT entries, but saw {1}".format(
                    expected_at_count, len(at_entries)
                )
            )
            if args.strict:
                continue

        for hap_index, allele_str in enumerate(alleles, 1):
            if allele_str == "0":
                continue

            try:
                allele_index = int(allele_str)
            except ValueError:
                counts["bad_allele_index"] += 1
                warn_record(rec, "bad GT allele index '{0}'; skipping allele".format(
                    allele_str
                ))
                continue

            if allele_index < 0 or allele_index >= len(at_paths):
                counts["allele_index_out_of_range"] += 1
                warn_record(
                    rec,
                    "GT allele {0} has no corresponding AT[{0}] entry; skipping allele".format(
                        allele_index
                    )
                )
                continue

            alt_path = at_paths[allele_index]

            if len(alt_path) == 0:
                counts["empty_alt_traversal"] += 1
                warn_record(rec, "AT[{0}] is empty; skipping allele".format(allele_index))
                continue

            # Sanity check: the alt traversal should usually share anchors with AT[0].
            if oriented_node_id(alt_path[0]) != oriented_node_id(at_paths[0][0]) or \
               oriented_node_id(alt_path[-1]) != oriented_node_id(at_paths[0][-1]):
                counts["anchor_mismatch"] += 1
                warn_record(
                    rec,
                    "AT[{0}] anchors do not match AT[0] anchors".format(allele_index)
                )
                if args.strict:
                    continue

            repl = Replacement(
                chrom=rec["chrom"],
                pos=rec["pos"],
                var_id=rec["id"],
                start=start,
                end=end,
                traversal=alt_path,
                allele_index=allele_index,
                gt=phased_gt,
                phase_source=phase_source,
            )

            if hap_index == 1:
                hap1.append(repl)
                counts["hap1_replacements"] += 1
            else:
                hap2.append(repl)
                counts["hap2_replacements"] += 1

    return hap1, hap2, counts


def warn_record(rec, msg):
    warn("{0}:{1} ID={2}: {3}".format(
        rec.get("chrom", "."),
        rec.get("pos", "."),
        rec.get("id", "."),
        msg
    ))


def validate_replacements(replacements, hap_name, strict):
    repls = sorted(replacements, key=lambda r: (r.start, r.end, r.pos, r.var_id))

    true_overlaps = []
    bookended = []

    prev = None
    for r in repls:
        if prev is not None:
            if r.start < prev.end:
                true_overlaps.append((prev, r))
            elif r.start == prev.end:
                # Single shared anchor node. This is okay only if traversals connect cleanly.
                # stricter check than originally suggested (using oriented_node_id wrapper); see convo
                if prev.traversal[-1] == r.traversal[0]:
                    bookended.append((prev, r))
                else:
                    true_overlaps.append((prev, r))
        prev = r

    if bookended:
        warn("{0}: found {1} bookended replacement pairs sharing one anchor node".format(
            hap_name, len(bookended)
        ))

    if true_overlaps:
        warn("{0}: found {1} true overlapping replacement pairs".format(
            hap_name, len(true_overlaps)
        ))

        for prev, cur in true_overlaps[:20]:
            warn(
                "{0}: true overlap: previous {1}:{2} ID={3} interval={4}-{5}; "
                "current {6}:{7} ID={8} interval={9}-{10}".format(
                    hap_name,
                    prev.chrom, prev.pos, prev.var_id, prev.start, prev.end,
                    cur.chrom, cur.pos, cur.var_id, cur.start, cur.end
                )
            )

        if strict:
            die("{0}: true overlapping replacements found; aborting in strict mode".format(
                hap_name
            ))

    return repls


def apply_replacements(ref_path, replacements):
    out = []
    cursor = 0
    prev_repl = None

    for r in replacements:
        if prev_repl is not None and r.start == prev_repl.end:
            # Bookended replacement sharing one anchor node.
            # The previous replacement already emitted this shared node,
            # so append the current traversal minus its first node.
            out.extend(r.traversal[1:])
            cursor = r.end + 1
        else:
            out.extend(ref_path[cursor:r.start])
            out.extend(r.traversal)
            cursor = r.end + 1

        prev_repl = r

    out.extend(ref_path[cursor:])
    return out


def write_walk(path, out_path, osample_name, ochr_name, ohap_index):
    with open(out_path, "w") as out:
        w_line = path_to_w_string(path)
        fields = ['W', osample_name, ohap_index, ochr_name, '*', '*', w_line]
        out.write('\t'.join(fields) + "\n")


def write_gfa_p(path, path_name, out_path):
    with open(out_path, "w") as out:
        out.write("P\t{0}\t{1}\t*\n".format(path_name, path_to_p_string(path)))


def write_replacement_log(replacements, out_path):
    with open(out_path, "w") as out:
        out.write("\t".join([
            "chrom",
            "pos",
            "id",
            "start_idx",
            "end_idx",
            "allele_index",
            "gt",
            "phase_source",
            "traversal",
        ]) + "\n")

        for r in replacements:
            out.write("\t".join([
                str(r.chrom),
                str(r.pos),
                str(r.var_id),
                str(r.start),
                str(r.end),
                str(r.allele_index),
                str(r.gt),
                str(r.phase_source),
                path_to_w_string(r.traversal),
            ]) + "\n")


def write_counts(counts, out_path):
    with open(out_path, "w") as out:
        for key in sorted(counts):
            out.write("{0}\t{1}\n".format(key, counts[key]))


def main():

    parser = argparse.ArgumentParser(
        description="Prototype graph haplotype traversal reconstruction from AT-tagged TSV."
    )

    parser.add_argument("--gfa", required=True, help="Input GFA.")
    parser.add_argument("--path-name", required=True,
                        help="Reference path name to extract from GFA.")
    parser.add_argument("--tsv", required=True,
                        help="TSV from bcftools query: CHROM POS ID REF ALT AT GT.")
    parser.add_argument("--out-prefix", required=True,
                        help="Output prefix.")
    parser.add_argument("--outsample-name", help="Sample name for output w-line")
    parser.add_argument("--outseq-id", help="chromosome for output w-line")
    parser.add_argument("--seed", type=int, default=1,
                        help="Random seed for phasing unphased genotypes. Default: 1.")
    parser.add_argument("--has-header", action="store_true",
                        help="Set if TSV has a header line.")
    parser.add_argument("--ignore-ref-orientation", action="store_true",
                        help="Allow AT[0] to match reference path by node ID only.")
    parser.add_argument("--non-strict", action="store_true",
                        help="Do not abort on overlaps or AT count mismatches.")
    parser.add_argument("--emit-gfa-p", action="store_true",
                        help="Also emit GFA P-lines for haplotype paths.")
    parser.add_argument("--progress-every", type=int, default=50000,
                    help="Log progress after this many TSV records. Default: 50000.")

    args = parser.parse_args()

    args.strict = not args.non_strict

    rng = random.Random(args.seed)

    log("Loading reference path from GFA...")
    ref_path = load_gfa_path(args.gfa, args.path_name)
    log("Loaded reference path with {0} oriented nodes.".format(
        len(ref_path)
    ))

    log("Building reference path index...")
    ref_index = build_ref_index(ref_path)
    log("Reference path index contains {0} unique oriented nodes.".format(
        len(ref_index["exact"])
    ))

    log("Reading TSV and building replacement intervals...")
    records = read_tsv_records(args.tsv, args.has_header)
    hap1_repls, hap2_repls, counts = build_replacements(records, ref_path, ref_index, rng, args)

    log("Validating replacement intervals...")
    hap1_repls = validate_replacements(hap1_repls, "hap1", args.strict)
    hap2_repls = validate_replacements(hap2_repls, "hap2", args.strict)

    log("Applying replacements...")
    hap1_path = apply_replacements(ref_path, hap1_repls)
    hap2_path = apply_replacements(ref_path, hap2_repls)

    hap1_walk = args.out_prefix + ".hap1.walk.txt"
    hap2_walk = args.out_prefix + ".hap2.walk.txt"

    write_walk(hap1_path, hap1_walk, args.outsample_name, args.outseq_id, "1")
    write_walk(hap2_path, hap2_walk, args.outsample_name, args.outseq_id, "2")

    write_replacement_log(hap1_repls, args.out_prefix + ".hap1.replacements.tsv")
    write_replacement_log(hap2_repls, args.out_prefix + ".hap2.replacements.tsv")
    write_counts(counts, args.out_prefix + ".counts.tsv")

    if args.emit_gfa_p:
        write_gfa_p(hap1_path, args.path_name + "_hap1",
                    args.out_prefix + ".hap1.path.gfa")
        write_gfa_p(hap2_path, args.path_name + "_hap2",
                    args.out_prefix + ".hap2.path.gfa")

    log("Done.")
    log("Wrote:")
    log("  {0}".format(hap1_walk))
    log("  {0}".format(hap2_walk))
    log("  {0}.hap1.replacements.tsv".format(args.out_prefix))
    log("  {0}.hap2.replacements.tsv".format(args.out_prefix))
    log("  {0}.counts.tsv".format(args.out_prefix))


if __name__ == "__main__":
    main()
