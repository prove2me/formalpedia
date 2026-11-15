-- Prove2me | Theorems.Thm_DirKECC1549_Main_reverse_scan_trace_invariants
-- name    : DirKECC1549.Main.reverse_scan_trace_invariants
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-14T15:50:45.122702+00:00
-- url     : https://prove2.me/theorems/d41265f0-cbb7-4414-bab3-89c063cf80f3
-- title:
--   Parent and discovery-order invariants of every reverse-scan trace
-- statement:
--   Let G be a finite directed multigraph with root r. Suppose a finite ReverseScanTrace from the initial state (identity parents, discovery list [r], and no scanned edges) ends at a parent map P, discovery list L, and scanned-edge set S. Then the root remains its own parent, L has no repeated vertices, and r belongs to L.
--
--   Every non-root vertex v in L has an original edge to its parent; the parent also belongs to L and has a smaller first-occurrence index:
--
--   $$
--   (v,P(v))\in E,\qquad P(v)\in L,\qquad
--   \mathrm{index}_L(P(v))<\mathrm{index}_L(v).
--   $$
--
--   Every scanned edge has its tail in the discovery list:
--
--   $$
--   e\in S\quad\Longrightarrow\quad\mathrm{tail}(e)\in L.
--   $$
--
--   The assertions hold at every finite trace state, with no completion, queue-scheduling, edge-scan uniqueness, or reachability assumption. They supply the graph-theoretic invariants needed by a machine implementation of reverse search.
-- source:
--   Derived trace-invariant/refinement obligation for the fixed-code partial-correctness target https://prove2.me/theorems/c2a72733-62b4-4cbf-9796-d1e147e7ced3, using ReverseScanTrace in Definitions.Def_DirKECC1549_Main_ReverseScanTrace. The abstract transitions describe instructions 87–110 of reverseSearchAlgorithm; input restoration occurs at instructions 111–145.

import Definitions.Def_DirKECC1549_Main_ReverseScanTrace
set_option autoImplicit false

namespace DirKECC1549.Main

theorem reverse_scan_trace_invariants {n m : ℕ} (G : Fin m → Fin n × Fin n) (r : Fin n)
    {par : Fin n → Fin n} {order : List (Fin n)} {scanned : Finset (Fin m)}
    (ht : ReverseScanTrace G r par order scanned) :
    par r = r ∧ order.Nodup ∧ r ∈ order ∧
      (∀ v ∈ order, v ≠ r → (∃ e, G e = (v, par v)) ∧ par v ∈ order ∧
        order.idxOf (par v) < order.idxOf v) ∧
      ∀ e ∈ scanned, (G e).1 ∈ order := by sorry

end DirKECC1549.Main
