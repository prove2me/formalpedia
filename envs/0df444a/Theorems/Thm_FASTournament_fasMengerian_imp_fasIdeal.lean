-- Prove2me | Theorems.Thm_FASTournament_fasMengerian_imp_fasIdeal
-- name    : FASTournament.fasMengerian_imp_fasIdeal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:57.243577+00:00
-- url     : https://prove2.me/theorems/fc109e2c-1398-4656-a9eb-6959c2d5a757
-- title:
--   Edmonds–Giles: FAS Mengerian implies FAS ideal
-- statement:
--   Let $G=(V,A)$ be a finite digraph. If the system $Nx\ge\mathbf 1,\ x\ge\mathbf 0$ is totally dual integral ($G$ is FAS Mengerian), then it defines an integral polyhedron ($G$ is FAS ideal).
--
--   This is implication (iii) ⇒ (ii) of Theorem 1.2: total dual integrality implies primal integrality.
--
--   Differences from the source:
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
--   - encoding: an integral polyhedron (the convex hull of all integral vectors it contains) → the published DiscreteConvex.MConvexSets.IsIntegralPolyhedron, P = convexHull ℝ (P ∩ ℤ^A); reason: the same definition (p.2)
--   - generalization: a tournament T → every finite digraph G; reason: total dual integrality implies primal integrality for every such system (Edmonds–Giles, as stated for digraphs on p.2); a tournament is a finite digraph
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26 ("Implication (iii) ⇒ (ii) holds, because total-dual integrality implies primal integrality")

import Mathlib
import Definitions.Def_FASTournament_FASIdeal
import Definitions.Def_FASTournament_FASMengerian

namespace FASTournament

/-- **FAS Mengerian ⇒ FAS ideal (Edmonds–Giles).**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26: "Implication (iii) ⇒ (ii) holds, because total-dual
integrality implies primal integrality (see Edmonds-Giles theorem [19] stated in Section 1)."

For every finite digraph `G`: if `Nx ≥ 1, x ≥ 0` is TDI then it defines an integral polyhedron.

**Formalization Note.** Stated for every finite digraph, not only tournaments. -/
theorem fasMengerian_imp_fasIdeal {V : Type*} [Fintype V] (G : Digraph V)
    (h : FASMengerian G) : FASIdeal G := by sorry

end FASTournament
