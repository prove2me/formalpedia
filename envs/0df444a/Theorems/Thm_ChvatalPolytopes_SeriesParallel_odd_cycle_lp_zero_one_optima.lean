-- Prove2me | Theorems.Thm_ChvatalPolytopes_SeriesParallel_odd_cycle_lp_zero_one_optima
-- name    : ChvatalPolytopes.SeriesParallel.odd_cycle_lp_zero_one_optima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:27:24.263684+00:00
-- url     : https://prove2.me/theorems/a53a0ef4-bcf1-4788-b498-a342daeb5921
-- title:
--   Theorem 7.1 — the odd-cycle LP and its dual have zero–one optima on series-parallel networks
-- statement:
--   Let $G=(V,E)$ be a finite series-parallel network, i.e. a graph containing no homeomorph of $K_4$. Consider the linear program
--   $$
--   \max\ \sum_{u\in V}x_u\quad\text{subject to (7.1)},
--   $$
--   where (7.1) is $0\le x_u\le1$ ($u\in V$), $x_v+x_w\le1$ ($vw\in E$), and $\sum_{u\in C}x_u\le\tfrac12(|C|-1)$ for every vertex set $C$ inducing an odd circuit in $G$. Then both this problem and its linear programming dual have zero–one optimal solutions:
--
--   1. there is a zero–one vector $x$ satisfying (7.1) with $\sum_u x_u\ge\sum_u x'_u$ for **every real** $x'$ satisfying (7.1);
--   2. there is a zero–one dual feasible point $(y,z,w)$ whose dual objective $\sum_u y_u+\sum_e z_e+\sum_C\tfrac12(|C|-1)w_C$ is at most that of **every real** dual feasible point.
--
--   In particular the maximum of the relaxation equals the stability number $\alpha(G)$, attained at a stable set, and a zero–one dual optimum certifies it by covering the vertices with vertices, edges and induced odd circuits.
--
--   **Formalization Note** The dual is the one fixed in the `OddCycleLP` definition file: $x\ge0$ as sign constraints, dual variables $y\ge0$ on vertices, $z\ge0$ on edges and $w\ge0$ on $Z(G)$, and the covering constraint $y_u+\sum_{e\ni u}z_e+\sum_{C\ni u}w_C\ge1$. Optimality is against all real feasible points of the respective program, not only zero–one ones. The theorem does not assume $V$ nonempty; for the empty graph both programs are trivial.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 151, Theorem 7.1

import Mathlib
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
import Definitions.Def_ChvatalPolytopes_SeriesParallel_OddCycleLP

namespace ChvatalPolytopes.SeriesParallel

/-- **Theorem 7.1** (Chvátal 1975, p. 151). Let `G = (V, E)` be a series-parallel network. Then
both the problem of maximizing `∑ (x_u : u ∈ V)` subject to (7.1) and its linear programming dual
have zero–one optimal solutions.

(a) Some zero–one vector `x` satisfying (7.1) has `∑ x_u ≥ ∑ x'_u` for every *real* `x'`
satisfying (7.1).
(b) Some zero–one dual feasible `(y, z, w)` has dual objective at most that of every real dual
feasible point. The dual is the one of `DualFeasible`/`dualValue` (`0 ≤ x_u` as sign
constraints). -/
theorem odd_cycle_lp_zero_one_optima {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G) :
    (∃ x : V → ℝ, (∀ u, x u = 0 ∨ x u = 1) ∧ OddCycleFeasible G x ∧
      ∀ x' : V → ℝ, OddCycleFeasible G x' → primalValue x' ≤ primalValue x) ∧
    (∃ (y : V → ℝ) (z : G.edgeSet → ℝ) (w : {C : Finset V // C ∈ oddCircuits G} → ℝ),
      (∀ u, y u = 0 ∨ y u = 1) ∧ (∀ e, z e = 0 ∨ z e = 1) ∧ (∀ C, w C = 0 ∨ w C = 1) ∧
      DualFeasible G y z w ∧
      ∀ (y' : V → ℝ) (z' : G.edgeSet → ℝ) (w' : {C : Finset V // C ∈ oddCircuits G} → ℝ),
        DualFeasible G y' z' w' → dualValue G y z w ≤ dualValue G y' z' w') := by sorry

end ChvatalPolytopes.SeriesParallel
