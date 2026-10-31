-- Prove2me | Theorems.Thm_FASTournament_F1_fasMengerian
-- name    : FASTournament.F1_fasMengerian
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:08.971886+00:00
-- url     : https://prove2.me/theorems/7360486a-93b4-482b-91ef-d1ab1b64bdf5
-- title:
--   $F_1$ is FAS Mengerian
-- statement:
--   The tournament $F_1$ (the regular tournament on five vertices, $F_1=G_1-v_6$) is FAS Mengerian.
--
--   The paper deduces it from Lemma 4.1, since $F_1$ arises from $G_1$ by deleting a vertex. Together with Lemma 4.1 it settles the two exceptional tournaments of Theorems 2.7 and 3.1.
--
--   Differences from the source:
--   - encoding: F1 of Figure 4 → F1 := the subdigraph of G1 induced by vertices 1, …, 5 (G1 − v6, p.26); reason: the paper states that F1 arises from G1 by deleting v6; G1 − v6 is the regular 5-tournament drawn in Figure 4
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26 ("Since F1 arises from G1 by deleting vertex v6 (see the labeling in Figure 5), from Lemma 4.1 we deduce that F1 is also FAS Mengerian")

import Mathlib
import Definitions.Def_FASTournament_FASMengerian
import Definitions.Def_FASTournament_F1

namespace FASTournament

/-- **`F₁` is FAS Mengerian.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26: "Since F1 arises from G1 by deleting vertex v6 (see the
labeling in Figure 5), from Lemma 4.1 we deduce that F1 is also FAS Mengerian." -/
theorem F1_fasMengerian : FASMengerian F1 := by sorry

end FASTournament
