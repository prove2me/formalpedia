-- Prove2me | Theorems.Thm_DERAggregation_Unregulated_proposition_1
-- name    : DERAggregation.Unregulated.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:24:57.342195+00:00
-- url     : https://prove2.me/theorems/dde66756-2690-49fc-ae90-600e0525df70
-- title:
--   Proposition 1, p. 8 — the benchmark dispatch (9) has a unique optimum, which is a competitive equilibrium at the (5a)-multipliers
-- statement:
--   Consider the networked market of the Setting under Assumptions 1 and 2, and assume the benchmark economic dispatch problem (9) is feasible (Assumption 3). Then:
--
--   1. (9) has a unique optimal solution $(h^*,(x-d)^*,y^*)$; write $z^*=(x-d)^*$.
--   2. Let $\lambda\in\mathbb R^K$ be any vector of optimal Lagrange multipliers of the nodal balance constraints (5a) at this optimum. Then each $z^*_i$ is an optimal solution of the prosumer's problem (1) at the price $\lambda^{k(i)}$ of her node, and each $y^*_j$ is an optimal solution of the generator's problem (3) at $\lambda^{k(j)}$.
--   3. At every prosumer whose node price is positive, (2) holds: $u_i'(C_i-z_i^*)=\lambda^{k(i)}$; at every generator whose node price is positive, (4) holds: $c_j'(y^*_j)=\lambda^{k(j)}$.
--
--   Thus solving the ISO's welfare maximization (9) yields a competitive equilibrium in which every market participant, taking the locational marginal price as given, is satisfied with the dispatch; this is the efficiency benchmark of the paper.
--
--   **Formalization Note** The paper states the first-order conditions (2) and (4) without a sign condition. On a congested network a node price can be nonpositive, and then (2), (4) have no solution (the derivatives are positive); the first-order conditions are stated at nodes with positive price, and item 2 states the competitive-equilibrium property at every node. The existence of multipliers is not claimed (the paper writes "Denote the optimal Lagrange multipliers…"); the statements hold for every multiplier vector.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 8, Proposition 1; proof pp. 41, (97)–(99)

import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting

namespace DERAggregation.Unregulated

open Set

/-- Proposition 1 (p. 8). Under Assumptions 1–3 the benchmark dispatch (9) has a unique optimal
solution `(h*, (x − d)*, y*)`. At it, for every vector `λ` of optimal Lagrange multipliers of
(5a), each `z*_i` solves the prosumer's problem (1) and each `y*_j` the generator's problem (3)
at the price of its node, and (2), (4) hold at every node with a positive price. -/
theorem proposition_1 {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J]
    [Fintype L] (M : Market K I J L) (h1 : Assumption1 M) (h2 : Assumption2 M)
    (h3 : ∃ h z y, FeasB M h z y) :
    (∃! w : (K → ℝ) × (I → ℝ) × (J → ℝ), IsOptB M w.1 w.2.1 w.2.2) ∧
      ∀ h z y, IsOptB M h z y → ∀ lam : K → ℝ, IsMultB M lam h z y →
        (∀ i, IsOptPros (M.u i) (M.C i) M.Z (lam (M.loc i)) (z i)) ∧
        (∀ j, IsOptGen (M.c j) (M.ylo j) (M.yhi j) (lam (M.gloc j)) (y j)) ∧
        (∀ i, 0 < lam (M.loc i) → deriv (M.u i) (M.C i - z i) = lam (M.loc i)) ∧
        (∀ j, 0 < lam (M.gloc j) → deriv (M.c j) (y j) = lam (M.gloc j)) := by sorry

end DERAggregation.Unregulated
