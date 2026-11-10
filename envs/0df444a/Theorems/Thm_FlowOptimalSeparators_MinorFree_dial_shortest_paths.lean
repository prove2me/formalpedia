-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_dial_shortest_paths
-- name    : FlowOptimalSeparators.MinorFree.dial_shortest_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:07:03.402201+00:00
-- url     : https://prove2.me/theorems/65b31e8d-e116-43e3-bf1e-1503b0deffb9
-- title:
--   Theorem 5 — Dial shortest paths in linear plus diameter time
-- statement:
--   There is one deterministic shortest-path code block and one absolute constant $C>0$ such that for every size and finite-distance bound $N,M,L$,
--   $$T_{\rm SSSP}(N,M,L)\le C(N+M+L).$$
--   The domain consists of undirected finite graphs with nonnegative integer edge lengths and finite within-component distances at most $L$. A query returns exact distances, unreachable flags, and an actual shortest-path parent tree. The routine works from any valid input prefix and initializes its work arrays, so it can be invoked inside the separator program.
--
--   The routine receives no diameter bound as input and satisfies the caller-preservation convention of the SSSP interface.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: an algorithm and its running time → one finite scalar arithmetic RAM program, unit-cost arithmetic and comparisons, indirect arrays, and charged independent uniform-index draws; reason: the paper does not specify a bit machine; the chunk brief fixes the arithmetic RAM reading, without graph or shortest-path oracles
--   - encoding: integer edge weights and finite shortest-path diameter → nonnegative integer edge lengths, with finite component-distance limits used only in analysis; reason: an undirected negative edge creates a negative cycle and does not have the source’s finite shortest-distance interpretation
--   - generalization: finite-diameter graph and any source → also disconnected graphs, reporting vertices outside the source component unreachable, with the same n+m+L bound; reason: run the same source-component bucket search and initialize the remaining flags; connected finite-diameter inputs are included
--   - encoding: O(n+m+D) for a query → one constant and one code block bounding the actual worst time for all limits N,M,L; reason: the supremum is over actual scalar executions, including arbitrary initialized or reused scratch memory
--   - encoding: a shortest-path subroutine used in the running-time reduction → a deterministic routine preserving register 0 and both memories outside its reserved scratch prefix, with distance limits used only in analysis; reason: a caller/callee memory convention permits composition without supplying diameter advice; standard array implementations fit the fixed scratch allowance
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 8, Theorem 5

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_ShortestPaths

open scoped ENNReal
set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Theorem 5, p.8: a deterministic finite SSSP routine, on the finite-distance,
nonnegative integer domain, with O(N+M+L) actual scalar work. Unreachable vertices are flagged. -/
theorem dial_shortest_paths :
    ∃ (C : ℝ) (code : List Instruction), 0 < C ∧ SSSPCorrect code true ∧
      ∀ N M L : ℕ,
        TSSSP code N M L ≤ ENNReal.ofReal (C * ((N : ℝ) + M + L)) := by sorry

end FlowOptimalSeparators.MinorFree
