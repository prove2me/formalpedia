-- Prove2me | Theorems.Thm_FASTournament_theorem_1_1
-- name    : FASTournament.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:48.607859+00:00
-- url     : https://prove2.me/theorems/effc3383-bd06-484b-8c0b-e2680124a4ba
-- title:
--   Theorem 1.1 (Chen et al.) — a tournament is Möbius-free iff cycle ideal iff cycle Mengerian
-- statement:
--   For a finite tournament $T$, the following statements are equivalent:
--
--   1. $T$ is Möbius-free;
--   2. $T$ is cycle ideal; and
--   3. $T$ is cycle Mengerian.
--
--   This is the authors' earlier characterization (Chen et al., refs. [11, 12]); Theorem 1.2 is its blocker version, and the proof of Theorem 1.2 uses the equivalence of (1) and (2).
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: contains … as a subgraph → ContainsSubgraph: an injective vertex map sending every arc of the ladder to an arc of T (not necessarily induced); reason: the usual meaning of subgraph; the ladders are drawn on vertices u1, …, uk, taken as Fin k with index i − 1
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: an integral polyhedron (the convex hull of all integral vectors it contains) → the published DiscreteConvex.MConvexSets.IsIntegralPolyhedron, P = convexHull ℝ (P ∩ ℤ^A); reason: the same definition (p.2)
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 1.1, p.3

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_MobiusFree
import Definitions.Def_FASTournament_CycleIdeal
import Definitions.Def_FASTournament_CycleMengerian

namespace FASTournament

/-- **Theorem 1.1 (Chen et al. [11, 12]).**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 1.1, p.3: "For a tournament T, the following statements are equivalent:
(i) T is Möbius-free; (ii) T is cycle ideal; and (iii) T is cycle Mengerian."

For every finite tournament, Möbius-free, cycle ideal and cycle Mengerian are equivalent.

**Formalization Note.** Cycle ideal and cycle Mengerian are integrality and total dual
integrality of `Mx ≥ 1, x ≥ 0`, `M` the cycle-arc incidence matrix (p.2). -/
theorem theorem_1_1 {V : Type*} [Fintype V] (T : Digraph V) (hT : IsTournament T) :
    List.TFAE [MobiusFree T, CycleIdeal T, CycleMengerian T] := by sorry

end FASTournament
