#!/usr/bin/env python3

import argparse
import atexit
import datetime
import gzip
import gc
import hashlib
import math
import multiprocessing as mp
import os
import re
import resource
import sys
import time
from collections import Counter, defaultdict


# ---------------------------------------------------------------------------
# Logging / I/O helpers
# ---------------------------------------------------------------------------


def log(message):
    """Write a timestamped, immediately flushed progress message to stderr."""
    timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"{timestamp} {message}", file=sys.stderr, flush=True)


def parent_peak_rss_mib():
    """Return parent-process peak RSS in MiB on Linux/Unix, if available."""
    try:
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        # Linux reports KiB; macOS reports bytes. GRASER is primarily run on Linux.
        if sys.platform == "darwin":
            return rss / (1024.0 * 1024.0)
        return rss / 1024.0
    except Exception:
        return None


def _read_proc_status_kib(pid):
    """Read selected /proc/<pid>/status memory fields. Missing data is tolerated."""
    values = {"ppid": None, "rss_kib": None, "hwm_kib": None}
    try:
        with open(f"/proc/{pid}/status", "rt") as f:
            for line in f:
                if line.startswith("PPid:"):
                    values["ppid"] = int(line.split()[1])
                elif line.startswith("VmRSS:"):
                    values["rss_kib"] = int(line.split()[1])
                elif line.startswith("VmHWM:"):
                    values["hwm_kib"] = int(line.split()[1])
    except (OSError, ValueError, IndexError):
        pass
    return values


def _read_proc_smaps_rollup_kib(pid):
    """Read PSS/private/shared totals from /proc/<pid>/smaps_rollup when available."""
    wanted = {
        "Pss:": "pss_kib",
        "Private_Clean:": "private_clean_kib",
        "Private_Dirty:": "private_dirty_kib",
        "Private_Hugetlb:": "private_hugetlb_kib",
        "Shared_Clean:": "shared_clean_kib",
        "Shared_Dirty:": "shared_dirty_kib",
        "Shared_Hugetlb:": "shared_hugetlb_kib",
    }
    vals = {name: None for name in wanted.values()}
    try:
        with open(f"/proc/{pid}/smaps_rollup", "rt") as f:
            for line in f:
                fields = line.split()
                if not fields:
                    continue
                key = fields[0]
                if key in wanted and len(fields) >= 2:
                    vals[wanted[key]] = int(fields[1])
    except (OSError, ValueError, IndexError):
        pass

    def summed(keys):
        present = [vals[k] for k in keys if vals[k] is not None]
        return sum(present) if present else None

    return {
        "pss_kib": vals["pss_kib"],
        "private_kib": summed(("private_clean_kib", "private_dirty_kib", "private_hugetlb_kib")),
        "shared_kib": summed(("shared_clean_kib", "shared_dirty_kib", "shared_hugetlb_kib")),
    }


def process_memory_snapshot(pid):
    """Return current Linux process-memory metrics; unavailable fields are None."""
    status = _read_proc_status_kib(pid)
    rollup = _read_proc_smaps_rollup_kib(pid)
    return {
        "pid": pid,
        "ppid": status["ppid"],
        "rss_kib": status["rss_kib"],
        "hwm_kib": status["hwm_kib"],
        "pss_kib": rollup["pss_kib"],
        "private_kib": rollup["private_kib"],
        "shared_kib": rollup["shared_kib"],
    }


def _format_mib(kib):
    return "." if kib is None else f"{kib / 1024.0:.3f}"


def _format_bytes_mib(value):
    return "." if value is None else f"{value / (1024.0 * 1024.0):.3f}"


def _read_int_file(path):
    try:
        with open(path, "rt") as f:
            text = f.read().strip()
        if not text or text == "max":
            return None
        return int(text)
    except (OSError, ValueError):
        return None


def _read_key_value_int_file(path):
    values = {}
    try:
        with open(path, "rt") as f:
            for line in f:
                fields = line.split()
                if len(fields) >= 2:
                    try:
                        values[fields[0]] = int(fields[1])
                    except ValueError:
                        continue
    except OSError:
        pass
    return values


def _mountinfo_unescape(text):
    # mountinfo uses octal escapes for whitespace/backslash in path fields.
    return (
        text.replace("\\040", " ")
        .replace("\\011", "\t")
        .replace("\\012", "\n")
        .replace("\\134", "\\")
    )


def _resolve_cgroup_location():
    """Best-effort resolution of this process's memory cgroup (v2 or v1)."""
    cgroup_v2_path = None
    cgroup_v1_path = None
    try:
        with open("/proc/self/cgroup", "rt") as f:
            for line in f:
                line = line.rstrip("\n")
                parts = line.split(":", 2)
                if len(parts) != 3:
                    continue
                _, controllers, cg_path = parts
                if controllers == "":
                    cgroup_v2_path = cg_path
                elif "memory" in controllers.split(","):
                    cgroup_v1_path = cg_path
    except OSError:
        return None

    mounts = []
    try:
        with open("/proc/self/mountinfo", "rt") as f:
            for line in f:
                left, sep, right = line.partition(" - ")
                if not sep:
                    continue
                lf = left.split()
                rf = right.split()
                if len(lf) < 5 or len(rf) < 3:
                    continue
                mounts.append(
                    {
                        "root": _mountinfo_unescape(lf[3]),
                        "mountpoint": _mountinfo_unescape(lf[4]),
                        "fstype": rf[0],
                        "superopts": rf[2].split(","),
                    }
                )
    except OSError:
        return None

    def resolve(cg_path, candidates, version):
        if cg_path is None:
            return None
        # Prefer the most-specific matching cgroup mount root.
        matches = []
        for m in candidates:
            root = m["root"]
            if root == "/":
                rel = cg_path.lstrip("/")
            elif cg_path == root:
                rel = ""
            elif cg_path.startswith(root.rstrip("/") + "/"):
                rel = cg_path[len(root):].lstrip("/")
            else:
                continue
            fs_path = os.path.join(m["mountpoint"], rel)
            matches.append((len(root), fs_path, m))
        if not matches:
            return None
        _, fs_path, m = max(matches, key=lambda x: x[0])
        return {
            "version": version,
            "cgroup_path": cg_path,
            "fs_path": fs_path,
            "mountpoint": m["mountpoint"],
            "mount_root": m["root"],
        }

    v2_mounts = [m for m in mounts if m["fstype"] == "cgroup2"]
    info = resolve(cgroup_v2_path, v2_mounts, 2)
    if info is not None:
        return info

    v1_mounts = [
        m for m in mounts
        if m["fstype"] == "cgroup" and "memory" in m["superopts"]
    ]
    return resolve(cgroup_v1_path, v1_mounts, 1)


def cgroup_memory_snapshot(info):
    """Return current cgroup memory metrics in bytes; unavailable fields are None."""
    if info is None:
        return None

    base = info["fs_path"]
    result = {
        "version": info["version"],
        "path": info["cgroup_path"],
        "current_bytes": None,
        "peak_bytes": None,
        "anon_bytes": None,
        "file_bytes": None,
        "shmem_bytes": None,
        "file_mapped_bytes": None,
        "file_dirty_bytes": None,
        "file_writeback_bytes": None,
        "kernel_bytes": None,
        "slab_bytes": None,
        "sock_bytes": None,
        "pagetables_bytes": None,
        "swap_bytes": None,
    }

    if info["version"] == 2:
        result["current_bytes"] = _read_int_file(os.path.join(base, "memory.current"))
        result["peak_bytes"] = _read_int_file(os.path.join(base, "memory.peak"))
        result["swap_bytes"] = _read_int_file(os.path.join(base, "memory.swap.current"))
        stat = _read_key_value_int_file(os.path.join(base, "memory.stat"))
        mapping = {
            "anon_bytes": "anon",
            "file_bytes": "file",
            "shmem_bytes": "shmem",
            "file_mapped_bytes": "file_mapped",
            "file_dirty_bytes": "file_dirty",
            "file_writeback_bytes": "file_writeback",
            "kernel_bytes": "kernel",
            "slab_bytes": "slab",
            "sock_bytes": "sock",
            "pagetables_bytes": "pagetables",
        }
        for out_key, stat_key in mapping.items():
            if stat_key in stat:
                result[out_key] = stat[stat_key]
    else:
        result["current_bytes"] = _read_int_file(os.path.join(base, "memory.usage_in_bytes"))
        result["peak_bytes"] = _read_int_file(os.path.join(base, "memory.max_usage_in_bytes"))
        memsw = _read_int_file(os.path.join(base, "memory.memsw.usage_in_bytes"))
        if memsw is not None and result["current_bytes"] is not None:
            result["swap_bytes"] = max(0, memsw - result["current_bytes"])

        stat = _read_key_value_int_file(os.path.join(base, "memory.stat"))

        def v1stat(name):
            # On cgroup v1, total_* includes descendants and is preferable when available.
            return stat.get("total_" + name, stat.get(name))

        result["anon_bytes"] = v1stat("rss")
        result["file_bytes"] = v1stat("cache")
        result["shmem_bytes"] = v1stat("shmem")
        result["file_mapped_bytes"] = v1stat("mapped_file")
        result["file_dirty_bytes"] = v1stat("dirty")
        result["file_writeback_bytes"] = v1stat("writeback")
        result["pagetables_bytes"] = v1stat("pgtable") or v1stat("pgtables")
        if result["swap_bytes"] is None:
            result["swap_bytes"] = v1stat("swap")
        result["slab_bytes"] = v1stat("slab")
        result["sock_bytes"] = v1stat("sock")

    return result


class MemoryReporter:
    """Optional, best-effort parent/worker memory telemetry for diagnostic runs."""

    HEADER = [
        "elapsed_s",
        "fragments",
        "alignments",
        "event",
        "role",
        "pid",
        "ppid",
        "rss_mib",
        "hwm_mib",
        "pss_mib",
        "private_mib",
        "shared_mib",
        "cgroup_version",
        "cgroup_path",
        "cgroup_current_mib",
        "cgroup_peak_mib",
        "cgroup_anon_mib",
        "cgroup_file_mib",
        "cgroup_shmem_mib",
        "cgroup_file_mapped_mib",
        "cgroup_file_dirty_mib",
        "cgroup_file_writeback_mib",
        "cgroup_kernel_mib",
        "cgroup_slab_mib",
        "cgroup_sock_mib",
        "cgroup_pagetables_mib",
        "cgroup_swap_mib",
    ]

    def __init__(self, path, interval_s, start_time):
        self.path = path
        self.interval_s = interval_s
        self.start_time = start_time
        self.next_due = time.monotonic()
        self.warned_no_proc = False
        self.warned_no_cgroup = False
        self.cgroup_info = _resolve_cgroup_location()
        out_dir = os.path.dirname(os.path.abspath(path))
        os.makedirs(out_dir, exist_ok=True)
        self.handle = open(path, "wt")
        self.handle.write("\t".join(self.HEADER) + "\n")
        self.handle.flush()

    def close(self):
        if self.handle is not None:
            self.handle.close()
            self.handle = None

    def due(self):
        return time.monotonic() >= self.next_due

    def _pool_worker_pids(self, pool):
        if pool is None:
            return []
        pids = []
        try:
            for proc in pool._pool:
                if proc.pid is not None and proc.is_alive():
                    pids.append(proc.pid)
        except Exception:
            pass
        return pids

    def _write_row(self, elapsed, fragments, alignments, event, role, snap):
        vals = [
            f"{elapsed:.3f}",
            str(fragments),
            str(alignments),
            event,
            role,
            str(snap.get("pid", ".")),
            "." if snap.get("ppid") is None else str(snap["ppid"]),
            _format_mib(snap.get("rss_kib")),
            _format_mib(snap.get("hwm_kib")),
            _format_mib(snap.get("pss_kib")),
            _format_mib(snap.get("private_kib")),
            _format_mib(snap.get("shared_kib")),
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
        ]
        self.handle.write("\t".join(vals) + "\n")

    def _write_cgroup_row(self, elapsed, fragments, alignments, event, snap):
        if snap is None:
            return
        vals = [
            f"{elapsed:.3f}",
            str(fragments),
            str(alignments),
            event,
            "cgroup_self",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            ".",
            str(snap.get("version", ".")),
            snap.get("path") or ".",
            _format_bytes_mib(snap.get("current_bytes")),
            _format_bytes_mib(snap.get("peak_bytes")),
            _format_bytes_mib(snap.get("anon_bytes")),
            _format_bytes_mib(snap.get("file_bytes")),
            _format_bytes_mib(snap.get("shmem_bytes")),
            _format_bytes_mib(snap.get("file_mapped_bytes")),
            _format_bytes_mib(snap.get("file_dirty_bytes")),
            _format_bytes_mib(snap.get("file_writeback_bytes")),
            _format_bytes_mib(snap.get("kernel_bytes")),
            _format_bytes_mib(snap.get("slab_bytes")),
            _format_bytes_mib(snap.get("sock_bytes")),
            _format_bytes_mib(snap.get("pagetables_bytes")),
            _format_bytes_mib(snap.get("swap_bytes")),
        ]
        self.handle.write("\t".join(vals) + "\n")

    def _write_aggregate(self, elapsed, fragments, alignments, event, role, snaps):
        if not snaps:
            return

        def total(field):
            vals = [s[field] for s in snaps if s.get(field) is not None]
            return sum(vals) if vals else None

        snap = {
            "pid": ".",
            "ppid": None,
            "rss_kib": total("rss_kib"),
            # Summing per-process historical high-water marks is not a meaningful
            # point-in-time aggregate, so leave aggregate HWM undefined.
            "hwm_kib": None,
            "pss_kib": total("pss_kib"),
            "private_kib": total("private_kib"),
            "shared_kib": total("shared_kib"),
        }
        self._write_row(elapsed, fragments, alignments, event, role, snap)

    def snapshot(self, event, fragments=0, alignments=0, pool=None, force=False):
        if not force and not self.due():
            return

        now = time.monotonic()
        elapsed = now - self.start_time
        parent_pid = os.getpid()
        worker_pids = self._pool_worker_pids(pool)

        parent = process_memory_snapshot(parent_pid)
        workers = [process_memory_snapshot(pid) for pid in worker_pids]

        if parent["rss_kib"] is None and not self.warned_no_proc:
            log(
                "WARNING: memory reporter could not read /proc process RSS; "
                "diagnostic fields may be unavailable on this system"
            )
            self.warned_no_proc = True

        self._write_row(elapsed, fragments, alignments, event, "parent", parent)
        for i, snap in enumerate(workers, start=1):
            self._write_row(elapsed, fragments, alignments, event, f"worker_{i}", snap)

        self._write_aggregate(
            elapsed, fragments, alignments, event, "workers_total", workers
        )
        self._write_aggregate(
            elapsed, fragments, alignments, event, "all_processes_total", [parent] + workers
        )

        cgroup = cgroup_memory_snapshot(self.cgroup_info)
        if cgroup is not None:
            self._write_cgroup_row(elapsed, fragments, alignments, event, cgroup)
        elif not self.warned_no_cgroup:
            log(
                "WARNING: memory reporter could not resolve/read this process's memory cgroup; "
                "cgroup diagnostic rows will be unavailable"
            )
            self.warned_no_cgroup = True

        self.handle.flush()

        if force:
            self.next_due = now + self.interval_s
        else:
            while self.next_due <= now:
                self.next_due += self.interval_s


def is_gzip_file(path):
    """Detect gzip by magic bytes rather than filename suffix."""
    with open(path, "rb") as f:
        return f.read(2) == b"\x1f\x8b"


def open_text_auto(path):
    """Open plain-text or gzip-compressed input transparently."""
    if is_gzip_file(path):
        return gzip.open(path, "rt")
    return open(path, "rt")


def normalize_path(path, base_dir=None):
    path = os.path.expandvars(os.path.expanduser(path))
    if base_dir is not None and not os.path.isabs(path):
        path = os.path.join(base_dir, path)
    return os.path.abspath(path)


def read_manifest(path):
    """
    Read a two-column manifest containing:

        contig<TAB>path

    A header is optional. Relative paths are resolved relative to the manifest.
    Additional columns are ignored.
    """
    path = normalize_path(path)
    base_dir = os.path.dirname(path)
    rows = []

    with open_text_auto(path) as f:
        first_data_seen = False
        for lineno, line in enumerate(f, start=1):
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue

            cols = line.split("\t")
            if len(cols) < 2:
                raise ValueError(
                    f"Manifest {path!r}, line {lineno}: expected at least 2 tab-separated columns"
                )

            if not first_data_seen:
                first_data_seen = True
                c0 = cols[0].strip().lower()
                c1 = cols[1].strip().lower()
                if c0 in {"contig", "chrom", "chromosome", "seqid"} and c1 in {
                    "path", "file", "gaf", "gfa"
                }:
                    continue

            contig = cols[0].strip()
            file_path = normalize_path(cols[1].strip(), base_dir=base_dir)
            if not contig:
                raise ValueError(f"Manifest {path!r}, line {lineno}: empty contig")
            rows.append((contig, file_path))

    if not rows:
        raise ValueError(f"Manifest {path!r} contained no input rows")

    return rows


# ---------------------------------------------------------------------------
# Graph / walk parsing
# ---------------------------------------------------------------------------


# Compact internal representation used by v2.6. Numeric GFA segment IDs are
# encoded with one orientation bit in a 32-bit field, then two oriented nodes
# are packed into one <=64-bit Python integer edge key.
NODE_FIELD_BITS = 32
NODE_FIELD_MASK = (1 << NODE_FIELD_BITS) - 1
MAX_SEGMENT_ID = (1 << (NODE_FIELD_BITS - 1)) - 1


def encode_node(segment_id, reverse=False):
    """Encode a non-negative numeric segment ID plus orientation into one int."""
    if segment_id < 0 or segment_id > MAX_SEGMENT_ID:
        raise ValueError(
            f"Numeric segment ID {segment_id} is outside the supported range 0..{MAX_SEGMENT_ID}"
        )
    return (segment_id << 1) | int(bool(reverse))


def decode_segment_id(oriented_node):
    """Return the unoriented numeric segment ID from an encoded node."""
    return oriented_node >> 1


def flip_token(token):
    """Flip the orientation bit of an encoded node."""
    return token ^ 1


def pack_edge(a, b):
    """Pack two encoded oriented nodes into one integer edge key."""
    if a < 0 or a > NODE_FIELD_MASK or b < 0 or b > NODE_FIELD_MASK:
        raise ValueError("Encoded node exceeds 32-bit edge-packing field")
    return (a << NODE_FIELD_BITS) | b


def parse_walk(walk_str):
    """
    Parse a W-line or GAF walk into compact oriented integer node IDs.

    v2.5 intentionally requires numeric GFA segment IDs for the compact
    publication-oriented code path. For example, '>12>34<56' becomes encoded
    integers equivalent to [(12<<1), (34<<1), (56<<1)|1].
    """
    nodes = []
    i = 0
    n = len(walk_str)

    while i < n:
        arrow = walk_str[i]
        if arrow not in (">", "<"):
            raise ValueError(
                f"Unexpected character {walk_str[i]!r} at position {i} in graph walk"
            )
        i += 1
        start = i
        while i < n and walk_str[i] not in (">", "<"):
            i += 1
        seg_text = walk_str[start:i]
        if not seg_text:
            raise ValueError("Empty segment ID in graph walk")
        try:
            segment_id = int(seg_text, 10)
        except ValueError as exc:
            raise ValueError(
                f"Compact indexing requires numeric GFA segment IDs; found {seg_text!r}"
            ) from exc
        if segment_id < 0:
            raise ValueError(
                f"Compact indexing requires non-negative numeric segment IDs; found {seg_text!r}"
            )
        nodes.append(encode_node(segment_id, reverse=(arrow == "<")))

    return nodes


def canonical_edge(a, b):
    """
    Orientation-independent packed edge key for contig routing.

    A forward edge (a,b) and its reverse traversal (rc(b),rc(a)) describe the
    same graph adjacency for contig ownership.
    """
    edge = pack_edge(a, b)
    rc_edge = pack_edge(b ^ 1, a ^ 1)
    return min(edge, rc_edge)


def is_autosome(contig):
    """Recognize human autosomes named 1..22 or chr1..chr22."""
    m = re.fullmatch(r"(?:chr)?([0-9]+)", contig, flags=re.IGNORECASE)
    if not m:
        return False
    n = int(m.group(1))
    return 1 <= n <= 22


def add_owner(owner_map, key, contig_id):
    """
    Store one compact integer contig ID directly; promote to a set only when a
    node/edge is observed in more than one canonical contig.
    """
    old = owner_map.get(key)
    if old is None:
        owner_map[key] = contig_id
    elif isinstance(old, int):
        if old != contig_id:
            owner_map[key] = {old, contig_id}
    else:
        old.add(contig_id)


def owner_set(owner_value):
    if owner_value is None:
        return None
    if isinstance(owner_value, int):
        return {owner_value}
    return set(owner_value)


def _w_line_header_positions(line):
    """Return the first six tab offsets for a W-line, or None if malformed."""
    pos = []
    start = 0
    for _ in range(6):
        i = line.find("\t", start)
        if i < 0:
            return None
        pos.append(i)
        start = i + 1
    return pos


def build_reference_index(
    gfa_sources,
    sample_id,
    hap_indices=(1, 2),
    autosomes_only=False,
    need_routing=False,
    check_contig_sharing=False,
    index_mode="contig",
):
    """
    Stream selected W-lines and construct either per-contig or global haplotype
    edge indexes, compact node haplotype indexes, and (when needed) a node-based
    contig-routing index.

    In contig mode, multiple W-lines for the same (sample, hap, contig) are
    unioned into one model per contig. In global mode, all selected W-lines for
    each haplotype are unioned directly into one whole-genome model.

    Every scoring model stores:
      pair_index         oriented edge -> hap bitmask
      node_index         unoriented segment ID -> hap bitmask
      edge_counts        per-haplotype unique-edge counts (for QC/statistics)
      node_counts        per-haplotype unique-node counts (for QC/statistics)
      union_edge_count   number of unique edges in H1 U H2; this is the common
                         denominator used for BOTH haplotypes during scoring
    """
    hap1, hap2 = hap_indices
    hap_to_bit = {hap1: 1, hap2: 2}
    wanted_haps = {str(hap1), str(hap2)}

    pair_indexes = defaultdict(dict) if index_mode == "contig" else None
    node_indexes = defaultdict(dict) if index_mode == "contig" else None
    global_pair_index = {} if index_mode == "global" else None
    global_node_index = {} if index_mode == "global" else None
    included_contigs = set()
    walk_line_counts = defaultdict(lambda: Counter())
    global_walk_line_counts = Counter()
    total_edge_counts = defaultdict(lambda: Counter())
    global_total_edge_counts = Counter()
    total_node_counts = defaultdict(lambda: Counter())
    global_total_node_counts = Counter()
    seqids_seen_by_manifest_contig = defaultdict(set)

    # Routing values use small integer contig IDs; strings are retained only in
    # this lookup table and in the scoring model/output dictionaries.
    contig_to_id = {}
    contig_names = []

    def get_contig_id(contig):
        cid = contig_to_id.get(contig)
        if cid is None:
            cid = len(contig_names)
            contig_to_id[contig] = cid
            contig_names.append(contig)
        return cid

    routing = {} if need_routing or check_contig_sharing else None
    edge_owners = {} if check_contig_sharing else None

    total_w_lines = 0
    selected_w_lines = 0
    malformed_w_lines = 0
    excluded_selected_w_lines = 0
    max_reference_segment_id = None

    for contig_hint, gfa_path in gfa_sources:
        log(
            f"Reading graph walks from {gfa_path}"
            + (f" (manifest contig {contig_hint})" if contig_hint else "")
        )

        with open_text_auto(gfa_path) as f:
            for line in f:
                if not line.startswith("W\t"):
                    continue
                total_w_lines += 1

                tabs = _w_line_header_positions(line)
                if tabs is None:
                    malformed_w_lines += 1
                    continue

                # Examine only small header slices before materializing the walk.
                t0, t1, t2, t3, t4, t5 = tabs
                rec_sample = line[t0 + 1:t1]
                rec_hap = line[t1 + 1:t2]
                if rec_sample != sample_id or rec_hap not in wanted_haps:
                    continue
                rec_seqid = line[t2 + 1:t3]

                selected_w_lines += 1
                hap = int(rec_hap)
                bit = hap_to_bit[hap]
                contig = contig_hint if contig_hint is not None else rec_seqid
                contig_id = get_contig_id(contig)

                if contig_hint is not None:
                    seqids_seen_by_manifest_contig[contig_hint].add(rec_seqid)

                walk_text = line[t5 + 1:]
                if walk_text.endswith("\n"):
                    walk_text = walk_text[:-1]
                try:
                    walk_nodes = parse_walk(walk_text)
                except ValueError as exc:
                    raise ValueError(
                        f"Failed to parse selected W-line in {gfa_path!r} "
                        f"(sample={rec_sample!r}, hap={rec_hap!r}, seqid={rec_seqid!r}): {exc}"
                    ) from exc

                excluded = autosomes_only and not is_autosome(contig)
                if excluded:
                    excluded_selected_w_lines += 1
                else:
                    included_contigs.add(contig)
                    walk_line_counts[contig][hap] += 1
                    global_walk_line_counts[hap] += 1

                for tok in walk_nodes:
                    segment_id = decode_segment_id(tok)
                    if max_reference_segment_id is None or segment_id > max_reference_segment_id:
                        max_reference_segment_id = segment_id

                    if routing is not None:
                        add_owner(routing, segment_id, contig_id)

                    if excluded:
                        continue

                    if index_mode == "contig":
                        node_indexes[contig][segment_id] = node_indexes[contig].get(segment_id, 0) | bit
                        total_node_counts[contig][hap] += 1
                    else:
                        global_node_index[segment_id] = global_node_index.get(segment_id, 0) | bit
                        global_total_node_counts[hap] += 1

                for a, b in zip(walk_nodes, walk_nodes[1:]):
                    if edge_owners is not None:
                        add_owner(edge_owners, canonical_edge(a, b), contig_id)

                    if excluded:
                        continue

                    key = pack_edge(a, b)
                    if index_mode == "contig":
                        pair_indexes[contig][key] = pair_indexes[contig].get(key, 0) | bit
                        total_edge_counts[contig][hap] += 1
                    else:
                        global_pair_index[key] = global_pair_index.get(key, 0) | bit
                        global_total_edge_counts[hap] += 1

    if selected_w_lines == 0:
        raise ValueError(
            f"No W-lines found for sample={sample_id!r} and hap indices {hap_indices}"
        )

    models = {}
    global_model = None
    missing_haps = []

    if index_mode == "contig":
        for contig in included_contigs:
            pair_index = pair_indexes[contig]
            node_index = node_indexes[contig]
            missing = [hap for hap in hap_indices if walk_line_counts[contig][hap] == 0]
            if missing:
                missing_haps.append((contig, missing))
                continue

            unique_edge_counts = {
                hap1: sum(1 for mask in pair_index.values() if mask & 1),
                hap2: sum(1 for mask in pair_index.values() if mask & 2),
            }
            unique_node_counts = {
                hap1: sum(1 for mask in node_index.values() if mask & 1),
                hap2: sum(1 for mask in node_index.values() if mask & 2),
            }

            models[contig] = {
                "pair_index": pair_index,
                "node_index": node_index,
                "edge_counts": unique_edge_counts,
                "node_counts": unique_node_counts,
                "union_edge_count": len(pair_index),
                "union_node_count": len(node_index),
                "total_edge_counts": {
                    hap1: total_edge_counts[contig][hap1],
                    hap2: total_edge_counts[contig][hap2],
                },
                "total_node_counts": {
                    hap1: total_node_counts[contig][hap1],
                    hap2: total_node_counts[contig][hap2],
                },
                "walk_line_counts": {
                    hap1: walk_line_counts[contig][hap1],
                    hap2: walk_line_counts[contig][hap2],
                },
            }

        if missing_haps:
            details = ", ".join(f"{contig}: missing {missing}" for contig, missing in missing_haps)
            raise ValueError(
                "Diploid contig scoring currently requires both requested haplotypes for every "
                f"included contig. {details}. Use --autosomes-only or remove unsupported paths."
            )

        if not models:
            raise ValueError("No diploid contig models remained after applying input filters")

    else:
        missing = [hap for hap in hap_indices if global_walk_line_counts[hap] == 0]
        if missing:
            raise ValueError(
                f"Global scoring requires at least one selected W-line for each haplotype; missing {missing}"
            )
        if not global_pair_index:
            raise ValueError("No edges remained in the global haplotype model")

        unique_edge_counts = {
            hap1: sum(1 for mask in global_pair_index.values() if mask & 1),
            hap2: sum(1 for mask in global_pair_index.values() if mask & 2),
        }
        unique_node_counts = {
            hap1: sum(1 for mask in global_node_index.values() if mask & 1),
            hap2: sum(1 for mask in global_node_index.values() if mask & 2),
        }
        global_model = {
            "pair_index": global_pair_index,
            "node_index": global_node_index,
            "edge_counts": unique_edge_counts,
            "node_counts": unique_node_counts,
            "union_edge_count": len(global_pair_index),
            "union_node_count": len(global_node_index),
            "total_edge_counts": {
                hap1: global_total_edge_counts[hap1],
                hap2: global_total_edge_counts[hap2],
            },
            "total_node_counts": {
                hap1: global_total_node_counts[hap1],
                hap2: global_total_node_counts[hap2],
            },
            "walk_line_counts": {
                hap1: global_walk_line_counts[hap1],
                hap2: global_walk_line_counts[hap2],
            },
        }

    shared_node_keys = 0
    if routing is not None:
        shared_node_keys = sum(1 for owners in routing.values() if not isinstance(owners, int))

    shared_edge_keys = 0
    if edge_owners is not None:
        shared_edge_keys = sum(1 for owners in edge_owners.values() if not isinstance(owners, int))

    # Preserve the manifest's original contract: each row describes an already
    # partitioned canonical contig input. General accession->chromosome mapping
    # remains intentionally out of scope for v2.6.
    multi_seqid_manifest_entries = {
        contig: sorted(seqids)
        for contig, seqids in seqids_seen_by_manifest_contig.items()
        if len(seqids) > 1
    }
    if index_mode == "contig" and multi_seqid_manifest_entries:
        details = "; ".join(
            f"{contig}: {seqids}" for contig, seqids in sorted(multi_seqid_manifest_entries.items())
        )
        raise ValueError(
            "Each --gfa-manifest row must describe a per-contig graph/W-line file in contig mode. "
            f"The following manifest entries contained multiple selected W-line SeqIds: {details}"
        )

    manifest_seqid_warnings = {
        contig: sorted(seqids)
        for contig, seqids in seqids_seen_by_manifest_contig.items()
        if len(seqids) == 1 and contig not in seqids
    }

    return {
        "index_mode": index_mode,
        "models": models,
        "global_model": global_model,
        "routing": routing,
        "routing_contigs": tuple(contig_names),
        "metadata": {
            "total_w_lines_seen": total_w_lines,
            "selected_w_lines": selected_w_lines,
            "malformed_w_lines": malformed_w_lines,
            "excluded_selected_w_lines": excluded_selected_w_lines,
            "shared_cross_contig_edges": shared_edge_keys,
            "shared_cross_contig_nodes": shared_node_keys,
            "manifest_seqid_warnings": manifest_seqid_warnings,
            "walk_line_counts": walk_line_counts,
            "node_encoding": "numeric_id_plus_orientation_bit_32bit",
            "edge_encoding": "two_32bit_oriented_nodes_packed_64bit",
            "routing_encoding": "unoriented_numeric_node_to_compact_contig_id",
            "max_reference_segment_id": max_reference_segment_id,
        },
    }


# ---------------------------------------------------------------------------
# Likelihood model -- intentionally preserves prototype logic
# ---------------------------------------------------------------------------


def loglik_by_hap(
    walk_nodes,
    pair_index,
    union_edge_count,
    hap_indices=(1, 2),
    epsilon=0.001,
    reverse=False,
):
    """
    Return log10 likelihoods per haplotype using one symmetric denominator:
    the number of unique edges in H1 U H2 for the active scoring scope.

    reverse=True scores the reverse-complement traversal directly from the
    original encoded walk, avoiding allocation of a full RC walk list while
    preserving the edge order used by the previous implementation.
    """
    hap1, hap2 = hap_indices
    c_union = max(int(union_edge_count), 1)
    inv_union = 1.0 / c_union

    l1 = 0.0
    l2 = 0.0
    n = len(walk_nodes)
    if n < 2:
        return {hap1: 0.0, hap2: 0.0}

    if reverse:
        edge_iter = ((walk_nodes[i] ^ 1, walk_nodes[i - 1] ^ 1) for i in range(n - 1, 0, -1))
    else:
        edge_iter = zip(walk_nodes, walk_nodes[1:])

    for a, b in edge_iter:
        mask = pair_index.get(pack_edge(a, b), 0)
        p1 = (epsilon + inv_union) if (mask & 1) else epsilon
        p2 = (epsilon + inv_union) if (mask & 2) else epsilon
        l1 += math.log10(p1)
        l2 += math.log10(p2)

    return {hap1: l1, hap2: l2}


def call_from_llr(llr, tau, hap_indices=(1, 2)):
    hap1, hap2 = hap_indices
    if llr > tau:
        return str(hap1)
    if llr < -tau:
        return str(hap2)
    return "ambiguous"


def classify_pair(call1, call2, hap_indices=(1, 2)):
    phased = {str(hap_indices[0]), str(hap_indices[1])}
    if call1 in phased and call2 in phased:
        return "concordant" if call1 == call2 else "discordant"
    if (call1 in phased and call2 == "ambiguous") or (
        call2 in phased and call1 == "ambiguous"
    ):
        return "partially_concordant"
    return "ambiguous"


def aggregate_fragment_call(call1, call2, hap_indices=(1, 2)):
    """Derive a fragment destination from the two preserved mate-level calls."""
    h1, h2 = str(hap_indices[0]), str(hap_indices[1])

    if call1 == h1 and call2 == h1:
        return h1
    if call1 == h2 and call2 == h2:
        return h2
    if {call1, call2} == {h1, h2}:
        return "discordant"
    if call1 == h1 or call2 == h1:
        return h1
    if call1 == h2 or call2 == h2:
        return h2
    return "ambiguous"


def call_single_walk_with_orientation_max(
    walk_nodes,
    pair_index,
    union_edge_count,
    hap_indices=(1, 2),
    epsilon=0.001,
    tau=1e-6,
):
    """Prototype single-read call: maximize each hap likelihood over orientation."""
    hap1, hap2 = hap_indices
    ll = loglik_by_hap(
        walk_nodes, pair_index, union_edge_count, hap_indices=hap_indices, epsilon=epsilon
    )
    ll_rc = loglik_by_hap(
        walk_nodes,
        pair_index,
        union_edge_count,
        hap_indices=hap_indices,
        epsilon=epsilon,
        reverse=True,
    )

    best_h1 = max(ll[hap1], ll_rc[hap1])
    best_h2 = max(ll[hap2], ll_rc[hap2])
    llr = best_h1 - best_h2

    return call_from_llr(llr, tau, hap_indices=hap_indices), llr


def call_pair_preserving_prototype_logic(
    w1,
    w2,
    pair_index,
    union_edge_count,
    hap_indices=(1, 2),
    epsilon=0.001,
    tau=1e-6,
):
    """
    Preserve the prototype paired-end orientation/LLR logic exactly, while
    returning an additional fragment-level aggregation for output routing.
    """
    hap1, hap2 = hap_indices

    w1_ll = loglik_by_hap(w1, pair_index, union_edge_count, hap_indices, epsilon)
    w1r_ll = loglik_by_hap(w1, pair_index, union_edge_count, hap_indices, epsilon, reverse=True)
    w2_ll = loglik_by_hap(w2, pair_index, union_edge_count, hap_indices, epsilon)
    w2r_ll = loglik_by_hap(w2, pair_index, union_edge_count, hap_indices, epsilon, reverse=True)

    # For each hap, choose the higher of the two opposite-mate orientation sums.
    A1 = w1_ll[hap1] + w2r_ll[hap1]
    B1 = w1r_ll[hap1] + w2_ll[hap1]
    if A1 >= B1:
        h1_m1 = w1_ll[hap1]
        h1_m2 = w2r_ll[hap1]
    else:
        h1_m1 = w1r_ll[hap1]
        h1_m2 = w2_ll[hap1]

    A2 = w1_ll[hap2] + w2r_ll[hap2]
    B2 = w1r_ll[hap2] + w2_ll[hap2]
    if A2 >= B2:
        h2_m1 = w1_ll[hap2]
        h2_m2 = w2r_ll[hap2]
    else:
        h2_m1 = w1r_ll[hap2]
        h2_m2 = w2_ll[hap2]

    llr_m1 = h1_m1 - h2_m1
    llr_m2 = h1_m2 - h2_m2

    call_m1 = call_from_llr(llr_m1, tau, hap_indices)
    call_m2 = call_from_llr(llr_m2, tau, hap_indices)
    pair_status = classify_pair(call_m1, call_m2, hap_indices)
    fragment_call = aggregate_fragment_call(call_m1, call_m2, hap_indices)

    return call_m1, llr_m1, call_m2, llr_m2, pair_status, fragment_call


# ---------------------------------------------------------------------------
# Read naming / contig routing
# ---------------------------------------------------------------------------


def canonical_fragment_name(qname):
    if qname.endswith("/1") or qname.endswith("/2"):
        return qname[:-2]
    return qname


def mate_suffix(qname):
    if qname.endswith("/1"):
        return "1"
    if qname.endswith("/2"):
        return "2"
    return None


def valid_pair_names(q1, q2):
    """
    Accept either the prototype convention (identical names) or conventional
    terminal /1 and /2 mate suffixes. Do not guess other naming conventions.
    """
    if q1 == q2:
        # Exact-name mate pairs are supported for the original GRASER test data,
        # but two records both explicitly labeled /1 or both /2 are not a pair.
        return mate_suffix(q1) is None
    if canonical_fragment_name(q1) != canonical_fragment_name(q2):
        return False
    return {mate_suffix(q1), mate_suffix(q2)} == {"1", "2"}


def route_walk_candidates(walk_nodes, routing):
    """
    Determine candidate compact contig IDs for a walk by intersecting ownership
    sets of all graph nodes present in the routing index.

    Unknown nodes provide no evidence. Shared nodes retain multiple candidates;
    contradictory node evidence produces an explicit conflict.
    """
    if routing is None or not walk_nodes:
        return None, "none"

    candidates = None
    matched_any = False

    for tok in walk_nodes:
        segment_id = decode_segment_id(tok)
        owners = routing.get(segment_id)
        if owners is None:
            continue

        matched_any = True
        current = owner_set(owners)
        if candidates is None:
            candidates = current
        else:
            candidates &= current
            if not candidates:
                return set(), "conflict"

    if not matched_any:
        return None, "none"
    if len(candidates) == 1:
        return candidates, "resolved"
    return candidates, "ambiguous"


def route_pair_contig(w1, w2, routing, routing_contigs):
    """Resolve a paired fragment to one canonical contig using both mates."""
    c1, s1 = route_walk_candidates(w1, routing)
    c2, s2 = route_walk_candidates(w2, routing)

    if s1 == "conflict" or s2 == "conflict":
        return None, "cross_contig_walk"

    nonempty = [c for c in (c1, c2) if c]
    if not nonempty:
        return None, "no_contig_match"

    candidates = set(nonempty[0])
    for c in nonempty[1:]:
        candidates &= c

    if not candidates:
        return None, "cross_contig_pair"
    if len(candidates) > 1:
        return None, "multi_contig_match"

    return routing_contigs[next(iter(candidates))], None


def route_single_contig(walk_nodes, routing, routing_contigs):
    candidates, status = route_walk_candidates(walk_nodes, routing)
    if status == "resolved":
        return routing_contigs[next(iter(candidates))], None
    if status == "conflict":
        return None, "cross_contig_walk"
    if status == "ambiguous":
        return None, "multi_contig_match"
    return None, "no_contig_match"


def deterministic_ambiguous_assignment(seed, contig, fragment_name, hap_indices=(1, 2)):
    """Stable 50/50 assignment independent of worker count or processing order."""
    payload = f"{seed}\0{contig}\0{fragment_name}".encode("utf-8")
    digest = hashlib.blake2b(payload, digest_size=8).digest()
    value = int.from_bytes(digest, byteorder="big", signed=False)
    return str(hap_indices[value & 1])


# ---------------------------------------------------------------------------
# Multiprocessing worker state / batch processing
# ---------------------------------------------------------------------------


_WORKER_MODELS = None
_WORKER_GLOBAL_MODEL = None
_WORKER_ROUTING = None
_WORKER_ROUTING_CONTIGS = ()
_WORKER_HAPS = (1, 2)
_WORKER_EPSILON = 0.001
_WORKER_TAU = 1e-6
_WORKER_READ_MODE = "paired"
_WORKER_RANDOMIZE_AMBIGUOUS = False
_WORKER_SEED = 1
_WORKER_AUTOSOMES_ONLY = False
_WORKER_INDEX_MODE = "contig"
_WORKER_RETURN_RECORDS = True


def set_worker_state(
    models,
    global_model,
    routing,
    routing_contigs,
    hap_indices,
    epsilon,
    tau,
    read_mode,
    randomize_ambiguous,
    seed,
    autosomes_only,
    index_mode,
    return_records,
):
    global _WORKER_MODELS
    global _WORKER_GLOBAL_MODEL
    global _WORKER_ROUTING
    global _WORKER_ROUTING_CONTIGS
    global _WORKER_HAPS
    global _WORKER_EPSILON
    global _WORKER_TAU
    global _WORKER_READ_MODE
    global _WORKER_RANDOMIZE_AMBIGUOUS
    global _WORKER_SEED
    global _WORKER_AUTOSOMES_ONLY
    global _WORKER_INDEX_MODE
    global _WORKER_RETURN_RECORDS

    _WORKER_MODELS = models
    _WORKER_GLOBAL_MODEL = global_model
    _WORKER_ROUTING = routing
    _WORKER_ROUTING_CONTIGS = tuple(routing_contigs)
    _WORKER_HAPS = tuple(hap_indices)
    _WORKER_EPSILON = epsilon
    _WORKER_TAU = tau
    _WORKER_READ_MODE = read_mode
    _WORKER_RANDOMIZE_AMBIGUOUS = randomize_ambiguous
    _WORKER_SEED = seed
    _WORKER_AUTOSOMES_ONLY = autosomes_only
    _WORKER_INDEX_MODE = index_mode
    _WORKER_RETURN_RECORDS = return_records


def worker_init_inherited():
    """Worker initializer for fork mode: retain inherited index and disable cyclic GC."""
    gc.disable()


def worker_init_with_state(*args):
    """Portable worker initializer for non-fork start methods."""
    set_worker_state(*args)
    gc.disable()


def gaf_qname(raw_line):
    """Extract only GAF field 1 without splitting/materializing the full record."""
    i = raw_line.find("\t")
    if i < 0:
        return raw_line.rstrip("\n")
    return raw_line[:i]


def parse_gaf_record(raw_line):
    """Extract only qname and path (GAF fields 1 and 6) from a raw record."""
    tabs = []
    start = 0
    for _ in range(5):
        i = raw_line.find("\t", start)
        if i < 0:
            qname = raw_line[:tabs[0]] if tabs else raw_line.rstrip("\n")
            return {"raw": raw_line, "qname": qname, "path": None, "error": "malformed_gaf"}
        tabs.append(i)
        start = i + 1

    qname = raw_line[:tabs[0]]
    path_start = tabs[4] + 1
    path_end = raw_line.find("\t", path_start)
    if path_end < 0:
        path = raw_line[path_start:].rstrip("\n")
    else:
        path = raw_line[path_start:path_end]
    return {"raw": raw_line, "qname": qname, "path": path, "error": None}


def make_unassigned_result(fragment_name, known_contig, records, reason):
    summaries = []
    for i, rec in enumerate(records, start=1):
        summaries.append(
            {
                "qname": rec.get("qname", ""),
                "fragment": fragment_name,
                "mate_index": i,
                "contig": known_contig or ".",
                "mate_call": ".",
                "llr": ".",
                "pair_status": "unassigned",
                "fragment_call": "unassigned",
                "output_assignment": "unassigned",
                "reason": reason,
            }
        )

    return {
        "fragment": fragment_name,
        "contig": known_contig,
        "raw_fragment_call": "unassigned",
        "output_assignment": "unassigned",
        "pair_status": "unassigned",
        "reason": reason,
        "alignment_count": len(records),
        "records": [rec["raw"] for rec in records] if _WORKER_RETURN_RECORDS else [],
        "summaries": summaries,
    }


def resolve_contig_for_group(contig_hint, walks):
    if contig_hint is not None:
        if _WORKER_AUTOSOMES_ONLY and not is_autosome(contig_hint):
            return contig_hint, "excluded_contig"
        if contig_hint not in _WORKER_MODELS:
            return contig_hint, "no_model_for_contig"
        return contig_hint, None

    if _WORKER_READ_MODE == "paired":
        contig, reason = route_pair_contig(walks[0], walks[1], _WORKER_ROUTING, _WORKER_ROUTING_CONTIGS)
    else:
        contig, reason = route_single_contig(walks[0], _WORKER_ROUTING, _WORKER_ROUTING_CONTIGS)

    if contig is None:
        return None, reason
    if _WORKER_AUTOSOMES_ONLY and not is_autosome(contig):
        return contig, "excluded_contig"
    if contig not in _WORKER_MODELS:
        return contig, "no_model_for_contig"

    return contig, None


def resolve_model_for_group(contig_hint, walks):
    """Return (contig, model, reason) for the configured scoring mode."""
    if _WORKER_INDEX_MODE == "global":
        if _WORKER_GLOBAL_MODEL is None:
            return None, None, "no_global_model"
        return None, _WORKER_GLOBAL_MODEL, None

    contig, reason = resolve_contig_for_group(contig_hint, walks)
    if reason is not None:
        return contig, None, reason
    return contig, _WORKER_MODELS[contig], None


def finalize_output_assignment(fragment_call, contig, fragment_name, allow_randomization=True):
    if fragment_call == "ambiguous" and _WORKER_RANDOMIZE_AMBIGUOUS and allow_randomization:
        return deterministic_ambiguous_assignment(
            _WORKER_SEED, contig, fragment_name, _WORKER_HAPS
        ), "randomized_ambiguous"
    return fragment_call, ""


def single_node_rescue(walks, node_index):
    """
    Return (call, status) from single-node-only evidence.

    status is one of: none, rescued, conflict. Shared/unknown nodes contribute
    no evidence. Multiple informative single-node pieces must agree.
    """
    evidence = set()
    h1, h2 = str(_WORKER_HAPS[0]), str(_WORKER_HAPS[1])
    for walk in walks:
        if len(walk) != 1:
            continue
        mask = node_index.get(decode_segment_id(walk[0]), 0)
        if mask == 1:
            evidence.add(h1)
        elif mask == 2:
            evidence.add(h2)

    if len(evidence) == 1:
        return next(iter(evidence)), "rescued"
    if len(evidence) > 1:
        return "ambiguous", "conflict"
    return "ambiguous", "none"


def process_group(group):
    """Process one complete qname group. Executed in a worker process."""
    fragment_name, contig_hint, raw_lines = group
    records = [parse_gaf_record(line) for line in raw_lines]

    if any(rec["error"] for rec in records):
        return make_unassigned_result(fragment_name, contig_hint, records, "malformed_gaf")

    if _WORKER_READ_MODE == "paired":
        if len(records) != 2:
            reason = "incomplete_pair" if len(records) == 1 else "unexpected_group_size"
            return make_unassigned_result(fragment_name, contig_hint, records, reason)

        q1 = records[0]["qname"]
        q2 = records[1]["qname"]
        if not valid_pair_names(q1, q2):
            return make_unassigned_result(fragment_name, contig_hint, records, "invalid_pair_names")

        paths = [records[0]["path"], records[1]["path"]]
        if any(not p or p == "*" or p[0] not in (">", "<") for p in paths):
            return make_unassigned_result(fragment_name, contig_hint, records, "unphaseable_pair")

        try:
            walks = [parse_walk(paths[0]), parse_walk(paths[1])]
        except ValueError:
            return make_unassigned_result(fragment_name, contig_hint, records, "invalid_walk")

        contig, model, reason = resolve_model_for_group(contig_hint, walks)
        if reason is not None:
            return make_unassigned_result(fragment_name, contig, records, reason)
        call1, llr1, call2, llr2, pair_status, fragment_call = call_pair_preserving_prototype_logic(
            walks[0],
            walks[1],
            model["pair_index"],
            model["union_edge_count"],
            hap_indices=_WORKER_HAPS,
            epsilon=_WORKER_EPSILON,
            tau=_WORKER_TAU,
        )

        rescue_status = "none"
        if fragment_call == "ambiguous":
            rescued_call, rescue_status = single_node_rescue(walks, model["node_index"])
            if rescue_status == "rescued":
                fragment_call = rescued_call

        if rescue_status == "rescued":
            output_assignment, assignment_reason = fragment_call, "single_node_rescue"
        elif rescue_status == "conflict":
            output_assignment, assignment_reason = finalize_output_assignment(
                fragment_call, contig, fragment_name, allow_randomization=False
            )
            assignment_reason = "single_node_rescue_conflict"
        else:
            output_assignment, assignment_reason = finalize_output_assignment(
                fragment_call, contig, fragment_name
            )

        summaries = []
        for i, (rec, mate_call, llr) in enumerate(
            ((records[0], call1, llr1), (records[1], call2, llr2)), start=1
        ):
            summaries.append(
                {
                    "qname": rec["qname"],
                    "fragment": fragment_name,
                    "mate_index": mate_suffix(rec["qname"]) or i,
                    "contig": contig if contig is not None else ".",
                    "mate_call": mate_call,
                    "llr": llr,
                    "pair_status": pair_status,
                    "fragment_call": fragment_call,
                    "output_assignment": output_assignment,
                    "reason": assignment_reason,
                }
            )

        return {
            "fragment": fragment_name,
            "contig": contig,
            "raw_fragment_call": fragment_call,
            "output_assignment": output_assignment,
            "pair_status": pair_status,
            "reason": assignment_reason,
            "alignment_count": len(records),
            "records": [rec["raw"] for rec in records] if _WORKER_RETURN_RECORDS else [],
            "summaries": summaries,
        }

    # Single-end mode
    if len(records) != 1:
        return make_unassigned_result(fragment_name, contig_hint, records, "unexpected_group_size")

    rec = records[0]
    path = rec["path"]
    if not path or path == "*" or path[0] not in (">", "<"):
        return make_unassigned_result(fragment_name, contig_hint, records, "unphaseable_read")

    try:
        walk = parse_walk(path)
    except ValueError:
        return make_unassigned_result(fragment_name, contig_hint, records, "invalid_walk")

    contig, model, reason = resolve_model_for_group(contig_hint, [walk])
    if reason is not None:
        return make_unassigned_result(fragment_name, contig, records, reason)
    call, llr = call_single_walk_with_orientation_max(
        walk,
        model["pair_index"],
        model["union_edge_count"],
        hap_indices=_WORKER_HAPS,
        epsilon=_WORKER_EPSILON,
        tau=_WORKER_TAU,
    )

    rescue_status = "none"
    if call == "ambiguous":
        rescued_call, rescue_status = single_node_rescue([walk], model["node_index"])
        if rescue_status == "rescued":
            call = rescued_call

    if rescue_status == "rescued":
        output_assignment, assignment_reason = call, "single_node_rescue"
    elif rescue_status == "conflict":
        output_assignment, assignment_reason = finalize_output_assignment(
            call, contig, fragment_name, allow_randomization=False
        )
        assignment_reason = "single_node_rescue_conflict"
    else:
        output_assignment, assignment_reason = finalize_output_assignment(call, contig, fragment_name)
    summary = {
        "qname": rec["qname"],
        "fragment": fragment_name,
        "mate_index": 1,
        "contig": contig if contig is not None else ".",
        "mate_call": call,
        "llr": llr,
        "pair_status": "single",
        "fragment_call": call,
        "output_assignment": output_assignment,
        "reason": assignment_reason,
    }

    return {
        "fragment": fragment_name,
        "contig": contig,
        "raw_fragment_call": call,
        "output_assignment": output_assignment,
        "pair_status": "single",
        "reason": assignment_reason,
        "alignment_count": 1,
        "records": [rec["raw"]] if _WORKER_RETURN_RECORDS else [],
        "summaries": [summary],
    }


def process_batch(batch):
    return [process_group(group) for group in batch]


# ---------------------------------------------------------------------------
# Streaming GAF grouping / batching
# ---------------------------------------------------------------------------


def iter_gaf_groups(gaf_sources, read_mode):
    """Yield (fragment_name, contig_hint, [raw GAF lines]) in input order."""
    malformed_counter = 0

    for contig_hint, gaf_path in gaf_sources:
        log(
            f"Reading alignments from {gaf_path}"
            + (f" (manifest contig {contig_hint})" if contig_hint else "")
        )

        with open_text_auto(gaf_path) as f:
            if read_mode == "single":
                for line in f:
                    if not line.strip() or line.startswith("#"):
                        continue
                    qname = gaf_qname(line)
                    fragment = canonical_fragment_name(qname) if qname else f"__malformed_{malformed_counter}"
                    if not qname:
                        malformed_counter += 1
                    yield (fragment, contig_hint, [line])
                continue

            current_fragment = None
            current_lines = []

            for line in f:
                if not line.strip() or line.startswith("#"):
                    continue

                qname = gaf_qname(line)
                if not qname:
                    fragment = f"__malformed_{malformed_counter}"
                    malformed_counter += 1
                else:
                    fragment = canonical_fragment_name(qname)

                if current_fragment is None:
                    current_fragment = fragment
                    current_lines = [line]
                elif fragment == current_fragment:
                    current_lines.append(line)
                else:
                    yield (current_fragment, contig_hint, current_lines)
                    current_fragment = fragment
                    current_lines = [line]

            if current_fragment is not None:
                yield (current_fragment, contig_hint, current_lines)


def iter_batches(group_iter, batch_size):
    batch = []
    for group in group_iter:
        batch.append(group)
        if len(batch) >= batch_size:
            yield batch
            batch = []
    if batch:
        yield batch


def ordered_bounded_pool_map(pool, func, iterable, max_outstanding):
    """
    Ordered multiprocessing map with an explicit bound on submitted/completed
    but not-yet-consumed tasks. The oldest outstanding task is always consumed
    first, preserving deterministic input/output order.
    """
    pending = []
    for item in iterable:
        pending.append(pool.apply_async(func, (item,)))
        if len(pending) >= max_outstanding:
            yield pending.pop(0).get()
    while pending:
        yield pending.pop(0).get()


# ---------------------------------------------------------------------------
# Outputs / statistics
# ---------------------------------------------------------------------------


def safe_contig_filename(contig):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", contig)


class OutputManager:
    SUMMARY_HEADER = [
        "qname",
        "fragment",
        "mate_index",
        "contig",
        "mate_call",
        "llr",
        "pair_status",
        "fragment_call",
        "output_assignment",
        "reason",
    ]

    def __init__(
        self, prefix, split_by_contig=False, compression="none", gzip_level=6, write_gaf=True
    ):
        self.prefix = prefix
        self.split_by_contig = split_by_contig
        self.compression = compression
        self.gzip_level = gzip_level
        self.write_gaf = write_gaf
        self.handles = {}

        out_dir = os.path.dirname(os.path.abspath(prefix))
        os.makedirs(out_dir, exist_ok=True)

        summary_path = prefix + ".summary.tsv"
        if compression == "gzip":
            summary_path += ".gz"
            self.summary = gzip.open(summary_path, "wt", compresslevel=gzip_level)
        else:
            self.summary = open(summary_path, "wt")
        self.summary_path = summary_path
        self.summary.write("\t".join(self.SUMMARY_HEADER) + "\n")

    def _open_gaf(self, contig, category):
        if category == "unassigned":
            key = (None, "unassigned")
            path = f"{self.prefix}.unassigned.gaf"
        elif self.split_by_contig:
            key = (contig, category)
            path = f"{self.prefix}.{safe_contig_filename(contig)}.{category}.gaf"
        else:
            key = (None, category)
            path = f"{self.prefix}.{category}.gaf"

        if key in self.handles:
            return self.handles[key]

        if self.compression == "gzip":
            path += ".gz"
            handle = gzip.open(path, "wt", compresslevel=self.gzip_level)
        else:
            handle = open(path, "wt")

        self.handles[key] = (handle, path)
        return self.handles[key]

    def write_result(self, result):
        raw_assignment = result["output_assignment"]
        if raw_assignment == str(_WORKER_HAPS[0]):
            category = "h1"
        elif raw_assignment == str(_WORKER_HAPS[1]):
            category = "h2"
        elif raw_assignment == "ambiguous":
            category = "ambiguous"
        elif raw_assignment == "discordant":
            category = "discordant"
        else:
            category = "unassigned"

        if self.write_gaf:
            handle, _ = self._open_gaf(result["contig"], category)
            for raw in result["records"]:
                handle.write(raw if raw.endswith("\n") else raw + "\n")

        for row in result["summaries"]:
            vals = []
            for key in self.SUMMARY_HEADER:
                val = row[key]
                if key == "llr" and isinstance(val, float):
                    vals.append(f"{val:.12g}")
                else:
                    vals.append(str(val))
            self.summary.write("\t".join(vals) + "\n")

    def close(self):
        for handle, _ in self.handles.values():
            handle.close()
        self.summary.close()

    def output_paths(self):
        return [path for _, path in self.handles.values()] + [self.summary_path]


class RunStats:
    def __init__(self):
        self.total_fragments = 0
        self.total_alignments = 0
        self.raw_calls = Counter()
        self.output_assignments = Counter()
        self.pair_status = Counter()
        self.reasons = Counter()
        self.contigs = Counter()

    def add(self, result):
        self.total_fragments += 1
        self.total_alignments += result.get("alignment_count", len(result["records"]))
        self.raw_calls[result["raw_fragment_call"]] += 1
        self.output_assignments[result["output_assignment"]] += 1
        self.pair_status[result["pair_status"]] += 1
        if result["reason"]:
            self.reasons[result["reason"]] += 1
        if result["contig"] is not None:
            self.contigs[result["contig"]] += 1


def write_stats(path, args, reference, run_stats, timings, output_paths):
    with open(path, "wt") as out:
        out.write("metric\tvalue\n")

        def emit(key, value):
            out.write(f"{key}\t{value}\n")

        md = reference["metadata"]
        emit("config.sample", args.sample)
        emit("config.read_mode", args.read_mode)
        emit("config.index_mode", args.index_mode)
        emit("config.threads", args.threads)
        emit("config.batch_size", args.batch_size)
        emit("config.max_outstanding_batches", args.max_outstanding_batches)
        emit("config.epsilon", args.epsilon)
        emit("config.tau", args.tau)
        emit("config.hap1_index", args.hap_indices[0])
        emit("config.hap2_index", args.hap_indices[1])
        emit("config.autosomes_only", args.autosomes_only)
        emit("config.split_by_contig", args.split_by_contig)
        emit("config.randomize_ambiguous", args.randomize_ambiguous)
        emit("config.seed", args.seed)
        emit("config.output_compression", args.output_compression)
        emit("config.summary_only", args.summary_only)

        emit("reference.contigs", len(reference["models"]))
        emit("reference.total_w_lines_seen", md["total_w_lines_seen"])
        emit("reference.selected_w_lines", md["selected_w_lines"])
        emit("reference.excluded_selected_w_lines", md["excluded_selected_w_lines"])
        emit("reference.malformed_w_lines", md["malformed_w_lines"])
        emit("reference.shared_cross_contig_edges", md["shared_cross_contig_edges"])
        emit("reference.shared_cross_contig_nodes", md["shared_cross_contig_nodes"])
        emit("reference.node_encoding", md.get("node_encoding", "."))
        emit("reference.edge_encoding", md.get("edge_encoding", "."))
        emit("reference.max_segment_id", md.get("max_reference_segment_id", "."))

        for contig in sorted(reference["models"]):
            model = reference["models"][contig]
            h1, h2 = args.hap_indices
            emit(f"reference.{contig}.hap{h1}.w_lines", model["walk_line_counts"][h1])
            emit(f"reference.{contig}.hap{h2}.w_lines", model["walk_line_counts"][h2])
            emit(f"reference.{contig}.hap{h1}.unique_edges", model["edge_counts"][h1])
            emit(f"reference.{contig}.hap{h2}.unique_edges", model["edge_counts"][h2])
            emit(f"reference.{contig}.union_unique_edges", model["union_edge_count"])
            emit(f"reference.{contig}.hap{h1}.unique_nodes", model["node_counts"][h1])
            emit(f"reference.{contig}.hap{h2}.unique_nodes", model["node_counts"][h2])
            emit(f"reference.{contig}.union_unique_nodes", model["union_node_count"])
            emit(f"reference.{contig}.hap{h1}.total_edges", model["total_edge_counts"][h1])
            emit(f"reference.{contig}.hap{h2}.total_edges", model["total_edge_counts"][h2])

        if reference.get("global_model") is not None:
            model = reference["global_model"]
            h1, h2 = args.hap_indices
            emit(f"reference.global.hap{h1}.w_lines", model["walk_line_counts"][h1])
            emit(f"reference.global.hap{h2}.w_lines", model["walk_line_counts"][h2])
            emit(f"reference.global.hap{h1}.unique_edges", model["edge_counts"][h1])
            emit(f"reference.global.hap{h2}.unique_edges", model["edge_counts"][h2])
            emit("reference.global.union_unique_edges", model["union_edge_count"])
            emit(f"reference.global.hap{h1}.unique_nodes", model["node_counts"][h1])
            emit(f"reference.global.hap{h2}.unique_nodes", model["node_counts"][h2])
            emit("reference.global.union_unique_nodes", model["union_node_count"])
            emit(f"reference.global.hap{h1}.total_edges", model["total_edge_counts"][h1])
            emit(f"reference.global.hap{h2}.total_edges", model["total_edge_counts"][h2])

        emit("run.fragments", run_stats.total_fragments)
        emit("run.alignments", run_stats.total_alignments)

        for key, value in sorted(run_stats.raw_calls.items()):
            emit(f"run.raw_call.{key}", value)
        for key, value in sorted(run_stats.output_assignments.items()):
            emit(f"run.output_assignment.{key}", value)
        for key, value in sorted(run_stats.pair_status.items()):
            emit(f"run.pair_status.{key}", value)
        for key, value in sorted(run_stats.reasons.items()):
            emit(f"run.reason.{key}", value)
        for key, value in sorted(run_stats.contigs.items()):
            emit(f"run.contig.{key}.fragments", value)

        for key, value in timings.items():
            emit(f"timing.{key}_seconds", f"{value:.3f}")

        rss = parent_peak_rss_mib()
        if rss is not None:
            emit("memory.parent_peak_rss_mib", f"{rss:.1f}")

        for i, output_path in enumerate(sorted(output_paths), start=1):
            emit(f"output.file.{i}", output_path)


# ---------------------------------------------------------------------------
# CLI / main
# ---------------------------------------------------------------------------


def build_arg_parser():
    parser = argparse.ArgumentParser(
        description=(
            "Phase graph-aligned GAF reads against two sample haplotype walks. "
            "Supports whole-genome or per-contig graph/alignment inputs, paired "
            "or single-end reads, gzip I/O, and multiprocessing."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    graph_group = parser.add_mutually_exclusive_group(required=True)
    graph_group.add_argument("--gfa", help="Whole-genome (or single-contig) GFA/W-line file")
    graph_group.add_argument(
        "--gfa-manifest",
        help="Two-column TSV: contig<TAB>GFA_path for per-contig graph inputs",
    )

    aln_group = parser.add_mutually_exclusive_group(required=True)
    aln_group.add_argument("--gaf", help="Whole-genome (or single-contig) GAF file")
    aln_group.add_argument(
        "--gaf-manifest",
        help="Two-column TSV: contig<TAB>GAF_path for per-contig alignment inputs",
    )

    parser.add_argument("--sample", required=True, help="GFA W-line SampleId to phase against")
    parser.add_argument(
        "--hap-indices",
        nargs=2,
        type=int,
        metavar=("HAP1", "HAP2"),
        default=(1, 2),
        help="Two W-line HapIndex values to compare",
    )
    parser.add_argument("--out-prefix", required=True, help="Prefix (optionally including a path) for outputs")
    parser.add_argument(
        "--index-mode",
        choices=("contig", "global"),
        default="contig",
        help=(
            "Score reads against per-contig haplotype edge models (contig) or one "
            "whole-genome H1/H2 edge union (global). Global mode skips contig routing."
        ),
    )

    parser.add_argument(
        "--read-mode",
        choices=("paired", "single"),
        default="paired",
        help="Require qname-grouped paired reads, or score each GAF record independently",
    )
    parser.add_argument(
        "--split-by-contig",
        action="store_true",
        help="Emit H1/H2/ambiguous/discordant GAFs separately for each resolved contig; unassigned remains global",
    )
    parser.add_argument(
        "--summary-only",
        action="store_true",
        help="Do not emit GAF files; write only summary/statistics outputs",
    )
    parser.add_argument(
        "--autosomes-only",
        action="store_true",
        help="Build phasing models only for human autosomes named 1-22 or chr1-chr22",
    )

    parser.add_argument(
        "--randomize-ambiguous",
        action="store_true",
        help="Reproducibly distribute ambiguous fragments between H1 and H2 output assignments",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=1,
        help="Seed used for deterministic ambiguous-fragment assignment",
    )

    parser.add_argument("--epsilon", type=float, default=0.001, help="Prototype edge-model epsilon")
    parser.add_argument("--tau", type=float, default=1e-6, help="Absolute LLR threshold for haplotype calls")

    parser.add_argument(
        "--threads",
        type=int,
        default=1,
        help="Number of worker processes used for read phasing",
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=5000,
        help="Approximate number of complete qname groups sent to each worker task",
    )
    parser.add_argument(
        "--max-outstanding-batches",
        type=int,
        default=None,
        help=(
            "Maximum submitted/completed worker batches awaiting ordered parent consumption; "
            "defaults to 2 * --threads"
        ),
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=500000,
        help="Log progress after this many processed fragments",
    )

    parser.add_argument(
        "--memory-report",
        help=(
            "Optional TSV path for diagnostic parent/worker and cgroup memory telemetry. "
            "On Linux, reports process RSS/HWM and, when permitted, PSS/private/shared memory, "
            "plus memory-cgroup total/anon/file/kernel accounting."
        ),
    )
    parser.add_argument(
        "--memory-report-every",
        type=float,
        default=60.0,
        help="Approximate seconds between periodic --memory-report snapshots",
    )

    parser.add_argument(
        "--output-compression",
        choices=("none", "gzip"),
        default="none",
        help="Compression for GAF and summary outputs",
    )
    parser.add_argument(
        "--gzip-level",
        type=int,
        choices=range(1, 10),
        default=6,
        metavar="1-9",
        help="gzip compression level for generated compressed outputs",
    )

    parser.add_argument(
        "--check-contig-sharing",
        action="store_true",
        help="Also build node ownership information and report nodes/edges shared across contigs",
    )
    parser.add_argument(
        "--fail-on-contig-sharing",
        action="store_true",
        help="Exit if cross-contig shared nodes or edges are detected; implies --check-contig-sharing",
    )

    return parser


def validate_args(args):
    if args.threads < 1:
        raise ValueError("--threads must be >= 1")
    if args.batch_size < 1:
        raise ValueError("--batch-size must be >= 1")
    if args.max_outstanding_batches is None:
        args.max_outstanding_batches = max(1, 2 * args.threads)
    elif args.max_outstanding_batches < 1:
        raise ValueError("--max-outstanding-batches must be >= 1")
    if args.progress_every < 1:
        raise ValueError("--progress-every must be >= 1")
    if args.memory_report_every <= 0:
        raise ValueError("--memory-report-every must be > 0")
    if args.epsilon <= 0:
        raise ValueError("--epsilon must be > 0")
    if args.tau < 0:
        raise ValueError("--tau must be >= 0")
    if args.hap_indices[0] == args.hap_indices[1]:
        raise ValueError("--hap-indices must specify two different HapIndex values")
    if args.index_mode == "global" and args.split_by_contig:
        raise ValueError("--split-by-contig is not available with --index-mode global")
    if args.fail_on_contig_sharing:
        args.check_contig_sharing = True


def sources_from_args(single_path, manifest_path):
    if single_path is not None:
        return [(None, normalize_path(single_path))]
    return read_manifest(manifest_path)


def main():
    parser = build_arg_parser()
    args = parser.parse_args()

    try:
        validate_args(args)
    except ValueError as e:
        parser.error(str(e))

    args.out_prefix = normalize_path(args.out_prefix)
    if args.memory_report is not None:
        args.memory_report = normalize_path(args.memory_report)
    gfa_sources = sources_from_args(args.gfa, args.gfa_manifest)
    gaf_sources = sources_from_args(args.gaf, args.gaf_manifest)

    for _, path in gfa_sources + gaf_sources:
        if not os.path.isfile(path):
            parser.error(f"Input file does not exist: {path}")

    whole_genome_gaf = args.gaf is not None
    need_routing = (args.index_mode == "contig" and whole_genome_gaf) or args.check_contig_sharing

    total_start = time.monotonic()
    memory_reporter = None
    if args.memory_report is not None:
        memory_reporter = MemoryReporter(
            args.memory_report, args.memory_report_every, total_start
        )
        atexit.register(memory_reporter.close)
        log(
            f"Diagnostic memory reporting enabled: {args.memory_report} "
            f"(approximately every {args.memory_report_every:g} s)"
        )
        if memory_reporter.cgroup_info is not None:
            cg = memory_reporter.cgroup_info
            log(
                f"Detected cgroup v{cg['version']} memory scope: {cg['cgroup_path']} "
                f"({cg['fs_path']})"
            )
        else:
            log("WARNING: no readable memory cgroup was detected for diagnostic reporting")
    log("GRASER read phasing started")
    log(
        f"Configuration: sample={args.sample}, read_mode={args.read_mode}, "
        f"index_mode={args.index_mode}, threads={args.threads}, "
        f"max_outstanding_batches={args.max_outstanding_batches}, "
        f"split_by_contig={args.split_by_contig}, summary_only={args.summary_only}, "
        f"autosomes_only={args.autosomes_only}, randomize_ambiguous={args.randomize_ambiguous}"
    )

    graph_start = time.monotonic()
    log(f"Building {args.index_mode} haplotype edge index...")
    reference = build_reference_index(
        gfa_sources,
        sample_id=args.sample,
        hap_indices=tuple(args.hap_indices),
        autosomes_only=args.autosomes_only,
        need_routing=need_routing,
        check_contig_sharing=args.check_contig_sharing,
        index_mode=args.index_mode,
    )
    graph_seconds = time.monotonic() - graph_start

    md = reference["metadata"]
    log(
        "Compact index encoding: numeric segment IDs + orientation bit; "
        "edges packed as two 32-bit oriented-node fields"
        + (
            f"; max reference segment ID={md['max_reference_segment_id']:,}"
            if md.get("max_reference_segment_id") is not None
            else ""
        )
    )
    if args.index_mode == "global":
        model = reference["global_model"]
        log(
            f"Reference index complete: 1 global model, "
            f"{model['union_edge_count']:,} unique edge keys in H1 U H2, "
            f"{md['selected_w_lines']:,} selected W-lines ({graph_seconds:.2f} s)"
        )
    else:
        total_model_edges = sum(len(model["pair_index"]) for model in reference["models"].values())
        log(
            f"Reference index complete: {len(reference['models'])} contig models, "
            f"{total_model_edges:,} contig-local unique edge keys, "
            f"{md['selected_w_lines']:,} selected W-lines ({graph_seconds:.2f} s)"
        )

    if reference["routing"] is not None:
        log(
            f"Routing index: {len(reference['routing']):,} node keys; "
            f"{md['shared_cross_contig_nodes']:,} are shared across contigs"
        )
    if args.check_contig_sharing:
        log(
            f"Contig-sharing check: {md['shared_cross_contig_nodes']:,} shared segment IDs, "
            f"{md['shared_cross_contig_edges']:,} shared adjacency keys"
        )

    for contig, seqids in md["manifest_seqid_warnings"].items():
        log(
            f"WARNING: GFA manifest contig {contig!r} contained W-line SeqId value(s) {seqids}; "
            "the manifest contig label is being used as the model/output contig"
        )

    if args.fail_on_contig_sharing and (
        md["shared_cross_contig_nodes"] > 0 or md["shared_cross_contig_edges"] > 0
    ):
        raise SystemExit(
            "Cross-contig node/edge sharing detected and --fail-on-contig-sharing was requested"
        )

    rss = parent_peak_rss_mib()
    if rss is not None:
        log(f"Parent peak RSS after reference indexing: {rss:.1f} MiB")

    if memory_reporter is not None:
        memory_reporter.snapshot("after_reference_index", force=True)

    # Initialize process-global read-only scoring state before forking. In
    # summary-only mode workers do not return raw GAF records to the parent.
    worker_state_args = (
        reference["models"],
        reference["global_model"],
        reference["routing"],
        reference["routing_contigs"],
        tuple(args.hap_indices),
        args.epsilon,
        args.tau,
        args.read_mode,
        args.randomize_ambiguous,
        args.seed,
        args.autosomes_only,
        args.index_mode,
        not args.summary_only,
    )
    set_worker_state(*worker_state_args)

    group_iter = iter_gaf_groups(gaf_sources, args.read_mode)
    batch_iter = iter_batches(group_iter, args.batch_size)

    # Create worker processes before opening buffered output streams so forked
    # workers do not inherit Python-level output buffers. Freeze long-lived
    # reference objects before fork to reduce copy-on-write page churn.
    pool = None
    if args.threads > 1:
        if "fork" in mp.get_all_start_methods():
            gc.collect()
            if hasattr(gc, "freeze"):
                gc.freeze()
            ctx = mp.get_context("fork")
            pool = ctx.Pool(
                processes=args.threads,
                initializer=worker_init_inherited,
            )
        else:
            log(
                "WARNING: multiprocessing 'fork' is unavailable; falling back to the platform "
                "default start method, which may use more memory for the reference index"
            )
            ctx = mp.get_context()
            pool = ctx.Pool(
                processes=args.threads,
                initializer=worker_init_with_state,
                initargs=worker_state_args,
            )

    outputs = None
    stats = RunStats()
    if memory_reporter is not None:
        memory_reporter.snapshot("after_worker_start", pool=pool, force=True)
    phase_start = time.monotonic()
    log("Starting read phasing...")
    next_progress = args.progress_every

    try:
        outputs = OutputManager(
            args.out_prefix,
            split_by_contig=args.split_by_contig,
            compression=args.output_compression,
            gzip_level=args.gzip_level,
            write_gaf=not args.summary_only,
        )

        if args.threads == 1:
            result_batches = map(process_batch, batch_iter)
        else:
            result_batches = ordered_bounded_pool_map(
                pool, process_batch, batch_iter, args.max_outstanding_batches
            )

        for result_batch in result_batches:
            for result in result_batch:
                outputs.write_result(result)
                stats.add(result)

            if memory_reporter is not None:
                memory_reporter.snapshot(
                    "phasing",
                    fragments=stats.total_fragments,
                    alignments=stats.total_alignments,
                    pool=pool,
                )

            if stats.total_fragments >= next_progress:
                elapsed = time.monotonic() - phase_start
                rate = stats.total_fragments / elapsed if elapsed > 0 else 0.0
                log(
                    f"Processed {stats.total_fragments:,} fragments "
                    f"({stats.total_alignments:,} GAF records) at {rate:,.0f} fragments/s"
                )
                while next_progress <= stats.total_fragments:
                    next_progress += args.progress_every

        if memory_reporter is not None:
            memory_reporter.snapshot(
                "phasing_complete_workers_alive",
                fragments=stats.total_fragments,
                alignments=stats.total_alignments,
                pool=pool,
                force=True,
            )

        if pool is not None:
            pool.close()
            pool.join()
            pool = None

        if memory_reporter is not None:
            memory_reporter.snapshot(
                "after_worker_join",
                fragments=stats.total_fragments,
                alignments=stats.total_alignments,
                pool=None,
                force=True,
            )

    finally:
        if pool is not None:
            pool.terminate()
            pool.join()
        if outputs is not None:
            outputs.close()
        if memory_reporter is not None:
            memory_reporter.close()

    phase_seconds = time.monotonic() - phase_start
    total_seconds = time.monotonic() - total_start

    stats_path = args.out_prefix + ".stats.tsv"
    output_paths = outputs.output_paths()
    output_paths.append(stats_path)
    write_stats(
        stats_path,
        args,
        reference,
        stats,
        timings={
            "reference_index": graph_seconds,
            "phasing_and_output": phase_seconds,
            "total": total_seconds,
        },
        output_paths=output_paths,
    )

    log(
        f"Phasing complete: {stats.total_fragments:,} fragments / "
        f"{stats.total_alignments:,} GAF records in {phase_seconds:.2f} s"
    )
    log(
        "Raw fragment calls: "
        + ", ".join(f"{k}={v:,}" for k, v in sorted(stats.raw_calls.items()))
    )
    log(
        "Output assignments: "
        + ", ".join(f"{k}={v:,}" for k, v in sorted(stats.output_assignments.items()))
    )
    if stats.reasons:
        log(
            "Special/unassigned reasons: "
            + ", ".join(f"{k}={v:,}" for k, v in sorted(stats.reasons.items()))
        )
    log(f"Statistics written to {stats_path}")
    log(f"GRASER read phasing complete ({total_seconds:.2f} s total)")


if __name__ == "__main__":
    main()

