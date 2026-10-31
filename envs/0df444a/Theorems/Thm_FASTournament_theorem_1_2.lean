-- Prove2me | Theorems.Thm_FASTournament_theorem_1_2
-- name    : FASTournament.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:09.173852+00:00
-- url     : https://prove2.me/theorems/f169b8c0-d6ef-47a3-801c-162ba20fcd86
-- title:
--   Theorem 1.2 — a tournament is Möbius-free iff FAS ideal iff FAS Mengerian
-- statement:
--   For a tournament $T$, the following statements are equivalent:
--
--   1. $T$ is Möbius-free, i.e. it contains none of the Möbius ladders $K_{3,3}$, $K'_{3,3}$, $M_5$, $M_5^*$ of Figure 1 as a subgraph;
--   2. $T$ is FAS ideal, i.e. $\{x\ge 0 : Nx\ge\mathbf 1\}$ is an integral polyhedron, $N$ the FAS-arc incidence matrix; and
--   3. $T$ is FAS Mengerian, i.e. the system $Nx\ge\mathbf 1,\ x\ge\mathbf 0$ is totally dual integral.
--
--   Equivalently (Edmonds–Giles), a tournament $T$ satisfies the packing–covering minimax $\lambda_w(T)=\mu_w(T)$ for every $w\in\mathbb Z_+^A$ exactly when it is Möbius-free. This is the blocker version of Theorem 1.1, with the same four obstructions.
--
--   **Formalization Note** The statement holds for every finite tournament, with no bound on the number of vertices and no strongness assumption; empty and acyclic tournaments are included (there both polyhedral properties hold vacuously).
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: contains … as a subgraph → ContainsSubgraph: an injective vertex map sending every arc of the ladder to an arc of T (not necessarily induced); reason: the usual meaning of subgraph; the ladders are drawn on vertices u1, …, uk, taken as Fin k with index i − 1
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: an integral polyhedron (the convex hull of all integral vectors it contains) → the published DiscreteConvex.MConvexSets.IsIntegralPolyhedron, P = convexHull ℝ (P ∩ ℤ^A); reason: the same definition (p.2)
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 1.2, p.4

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_MobiusFree
import Definitions.Def_FASTournament_FASIdeal
import Definitions.Def_FASTournament_FASMengerian

namespace FASTournament

/-- **Theorem 1.2.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 1.2, p.4: "For a tournament T, the following statements are equivalent:
(i) T is Möbius-free; (ii) T is FAS ideal; and (iii) T is FAS Mengerian."

For every finite tournament `T`, the three properties are equivalent.

**Formalization Note.** `T : Digraph V` on a finite type with `IsTournament T`; no bound on the
number of vertices and no strongness assumption (empty and acyclic tournaments are included).
FAS ideal is integrality of `{x ≥ 0 : Nx ≥ 1}` and FAS Mengerian is total dual integrality of
`Nx ≥ 1, x ≥ 0`, `N` the FAS-arc incidence matrix. -/
theorem theorem_1_2 {V : Type*} [Fintype V] (T : Digraph V) (hT : IsTournament T) :
    List.TFAE [MobiusFree T, FASIdeal T, FASMengerian T] := by sorry

end FASTournament
