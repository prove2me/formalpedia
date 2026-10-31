-- Prove2me | Theorems.Thm_FASTournament_lemma_3_2
-- name    : FASTournament.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:37.368867+00:00
-- url     : https://prove2.me/theorems/8d762662-581d-473e-9da4-1daa25d6bffe
-- title:
--   Lemma 3.2 — every tournament in $\mathcal Q$ is FAS Mengerian
-- statement:
--   Every tournament in the class $\mathcal Q$ (a center $v$ and sets $U_1,\dots,U_k$, each a singleton or a triangle, with all arcs between $U_i$ and $U_j$ directed to $U_j$ for $i<j$) is FAS Mengerian.
--
--   It is the base case of the induction on the number of vertical blocks that proves Theorem 3.1.
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: Q: the vertex set partitioned into U0, U1, …, Uk → InQ: a center c and a block index blk : V → ℕ with U_j = blk⁻¹(j), U0 = {c}, blk ≤ k; reason: the same partitions
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 3.2, p.13

import Mathlib
import Definitions.Def_FASTournament_InQ
import Definitions.Def_FASTournament_FASMengerian

namespace FASTournament

/-- **Lemma 3.2.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 3.2, p.13: "Every tournament in Q (see the paragraph succeeding Theorem 2.7) is FAS
Mengerian." -/
theorem lemma_3_2 {V : Type*} [Fintype V] (G : Digraph V) (hG : InQ G) :
    FASMengerian G := by sorry

end FASTournament
