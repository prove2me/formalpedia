-- Prove2me | Theorems.Thm_FASTournament_cycleIdeal_iff_fasIdeal
-- name    : FASTournament.cycleIdeal_iff_fasIdeal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:36.461391+00:00
-- url     : https://prove2.me/theorems/b280b787-bbf0-4236-b94f-743fcdb18c92
-- title:
--   Lehman: a tournament is cycle ideal iff it is FAS ideal
-- statement:
--   Let $T$ be a finite tournament. Then $T$ is cycle ideal (the polyhedron $\{x\ge 0: Mx\ge\mathbf 1\}$, $M$ the cycle-arc incidence matrix, is integral) if and only if $T$ is FAS ideal (the polyhedron $\{x\ge 0: Nx\ge\mathbf 1\}$, $N$ the FAS-arc incidence matrix, is integral).
--
--   The paper derives this from Lehman's theorem that a clutter is ideal iff its blocker is ideal; the minimal FASs form the blocker of the clutter of directed cycles.
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: an integral polyhedron (the convex hull of all integral vectors it contains) → the published DiscreteConvex.MConvexSets.IsIntegralPolyhedron, P = convexHull ℝ (P ∩ ℤ^A); reason: the same definition (p.2)
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26 ("It was proved by Lehman [29] that a clutter is ideal iff its blocker is ideal, which implies that a tournament is cycle ideal iff it is FAS ideal")

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_CycleIdeal
import Definitions.Def_FASTournament_FASIdeal

namespace FASTournament

/-- **A tournament is cycle ideal iff it is FAS ideal (Lehman).**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Theorem 1.2, p.26: "It was proved by Lehman [29] that a clutter is ideal iff its
blocker is ideal, which implies that a tournament is cycle ideal iff it is FAS ideal."

For every finite tournament `T`, the cycle polyhedron `{x ≥ 0 : Mx ≥ 1}` is integral iff the FAS
polyhedron `{x ≥ 0 : Nx ≥ 1}` is integral. -/
theorem cycleIdeal_iff_fasIdeal {V : Type*} [Fintype V] (T : Digraph V) (hT : IsTournament T) :
    CycleIdeal T ↔ FASIdeal T := by sorry

end FASTournament
