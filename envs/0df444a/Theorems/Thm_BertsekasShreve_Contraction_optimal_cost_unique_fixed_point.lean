-- Prove2me | Theorems.Thm_BertsekasShreve_Contraction_optimal_cost_unique_fixed_point
-- name    : BertsekasShreve.Contraction.optimal_cost_unique_fixed_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:14:10.884987+00:00
-- url     : https://prove2.me/theorems/582b16b5-d4ef-41e5-9624-8c38828938da
-- title:
--   Proposition 4.2 — $J^*$ is the unique fixed point of $T$ in $\bar B$, and value iteration converges
-- statement:
--   Let Assumption C hold for a model with closed set $\bar B\subseteq B$ and scalars $m,\rho,\alpha$, and let $J^*=\inf_{\pi\in\Pi}J_\pi$ be the optimal cost function. Then:
--
--   1. $J^*$ belongs to $\bar B$ and is the unique fixed point of $T$ within $\bar B$:
--   $$J^*=T(J^*),$$
--   and if $J'\in\bar B$ and $J'=T(J')$ then $J'=J^*$. Furthermore, if $J'\in\bar B$ satisfies $T(J')\le J'$ then $J^*\le J'$, while if $J'\le T(J')$ then $J'\le J^*$.
--   2. For every $\mu\in M$, the cost function $J_\mu$ of the stationary policy $(\mu,\mu,\dots)$ belongs to $\bar B$ and is the unique fixed point of $T_\mu$ within $\bar B$.
--   3. For every $J\in\bar B$ and $\mu\in M$,
--   $$\lim_{N\to\infty}\|T^N(J)-J^*\|=0,\qquad\lim_{N\to\infty}\|T_\mu^N(J)-J_\mu\|=0.$$
--
--   This is the central result of the contraction theory of abstract dynamic programming: Bellman's equation characterizes the optimal cost among all functions of $\bar B$, and successive approximation from any starting point of $\bar B$ converges to it in the supremum norm.
--
--   **Formalization Note** $J^*$ is the infimum over all policies, not only stationary ones; it is not defined as a fixed point. "$\lim_N\|T^N(J)-J^*\|=0$" is stated as: for every $\varepsilon>0$ there is $N_0$ with $\|T^N(J)-J^*\|\le\varepsilon$ for all $N\ge N_0$, with `SupDistLe` for the norm bound.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 55, Proposition 4.2

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.2, p. 55. Under Assumption C:
(a) `J* ∈ B̄`, `J* = T(J*)`, and `J*` is the only fixed point of `T` in `B̄`; if `J' ∈ B̄` and
`T(J') ≤ J'` then `J* ≤ J'`, while if `J' ≤ T(J')` then `J' ≤ J*`;
(b) for every `μ ∈ M`, `J_μ ∈ B̄` and `J_μ` is the unique fixed point of `T_μ` in `B̄`;
(c) `‖T^N(J) − J*‖ → 0` and `‖T_μ^N(J) − J_μ‖ → 0` for every `J ∈ B̄`, `μ ∈ M`. -/
theorem optimal_cost_unique_fixed_point {S C : Type*} (P : Model S C) (Bbar : Set (BFun S))
    (m : ℕ) (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    ((∃ Js ∈ Bbar, P.Jstar = toF Js) ∧
      P.T P.Jstar = P.Jstar ∧
      (∀ J ∈ Bbar, P.T (toF J) = toF J → toF J = P.Jstar) ∧
      (∀ J ∈ Bbar, P.T (toF J) ≤ toF J → P.Jstar ≤ toF J) ∧
      (∀ J ∈ Bbar, toF J ≤ P.T (toF J) → toF J ≤ P.Jstar)) ∧
    (∀ μ : P.Selector,
      (∃ Jm ∈ Bbar, P.Jmu μ = toF Jm) ∧
      P.Tmu μ (P.Jmu μ) = P.Jmu μ ∧
      (∀ J ∈ Bbar, P.Tmu μ (toF J) = toF J → toF J = P.Jmu μ)) ∧
    ((∀ J ∈ Bbar, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        SupDistLe (P.T^[N] (toF J)) P.Jstar ε) ∧
      (∀ μ : P.Selector, ∀ J ∈ Bbar, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        SupDistLe ((P.Tmu μ)^[N] (toF J)) (P.Jmu μ) ε)) := by sorry

end BertsekasShreve.Contraction
