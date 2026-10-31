-- Prove2me | Theorems.Thm_FASTournament_lemma_4_1
-- name    : FASTournament.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:18.363555+00:00
-- url     : https://prove2.me/theorems/96540b3c-d506-4b0d-bc32-996c6e697772
-- title:
--   Lemma 4.1 — $G_1$ is FAS Mengerian
-- statement:
--   The tournament $G_1$ (vertices $1,\dots,6$, arcs $12,23,34,45,51,13,35,52,24,41,16,26,63,64,65$) is FAS Mengerian: the system $Nx\ge\mathbf 1,\ x\ge\mathbf 0$, $N$ its FAS-arc incidence matrix, is totally dual integral.
--
--   $G_1$ is one of the two Möbius-free strong tournaments outside the class $\mathcal P$; the paper proves this lemma with a computer-assisted application of Lemma 4.3 (Claims 1–4).
--
--   Differences from the source:
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 4.1, p.23

import Mathlib
import Definitions.Def_FASTournament_FASMengerian
import Definitions.Def_FASTournament_G1

namespace FASTournament

/-- **Lemma 4.1.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 4.1, p.23: "Tournament G1 is FAS Mengerian." -/
theorem lemma_4_1 : FASMengerian G1 := by sorry

end FASTournament
