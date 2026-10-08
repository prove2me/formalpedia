-- Prove2me | Theorems.Thm_BertsekasShreve_Monotone_prop5_6_eps_optimal_from_bellman
-- name    : BertsekasShreve.Monotone.prop5_6_eps_optimal_from_bellman
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:19:50.804819+00:00
-- url     : https://prove2.me/theorems/199db388-5739-4986-8287-953b84163005
-- title:
--   Proposition 5.6 — near-attainment in Bellman's equation gives ε-optimal policies under I, I.1, I.2
-- statement:
--   In the abstract monotone dynamic programming model (state space $S$, constraint sets $U(x)$, monotone mapping $H$, terminal function $J_0$, operators $T_\mu$ and $T$, policy costs $J_\pi$, stationary costs $J_\mu$ and optimal cost $J^*=\inf_\pi J_\pi$), assume Assumptions I and I.1 hold, and Assumption I.2 holds with the scalar $\alpha>0$:
--   $$H(x,u,J)\le H(x,u,J+r)\le H(x,u,J)+\alpha r\qquad\text{for all } r>0,\ J\ge J_0,\ x\in S,\ u\in U(x).$$
--
--   1. Let $\varepsilon>0$ and let $\varepsilon_0,\varepsilon_1,\dots>0$ satisfy $\sum_{k=0}^\infty\alpha^k\varepsilon_k=\varepsilon$. If the policy $\pi^*=(\mu_0^*,\mu_1^*,\dots)$ satisfies
--   $$T_{\mu_k^*}(J^*)\le T(J^*)+\varepsilon_k,\qquad k=0,1,\dots,$$
--   then
--   $$J^*\le J_{\pi^*}\le J^*+\varepsilon.$$
--   2. Let $\varepsilon>0$, let $\alpha<1$, and let the selector $\mu^*$ satisfy $T_{\mu^*}(J^*)\le T(J^*)+\varepsilon(1-\alpha)$. Then
--   $$J^*\le J_{\mu^*}\le J^*+\varepsilon.$$
--
--   The result turns approximate attainment of the infimum in the optimality equation $J^*=T(J^*)$ into an explicit $\varepsilon$-optimal policy, which is stationary when $\alpha<1$; it is the substitute for Proposition 5.4 when the infimum is not attained.
--
--   **Formalization Note** The model and assumptions are the published `MonotoneDP.Increase` definitions; $\alpha$ is the scalar for which `AssumptionI2 α` is assumed. The series condition is `HasSum (fun k => α ^ k * εs k) ε`. Inequalities between functions are pointwise in $[-\infty,\infty]$; adding the real $\varepsilon$ to $+\infty$ gives $+\infty$. Under I, $J^*\ge J_0>-\infty$, so the $-\infty$ case of the book's $\varepsilon$-optimality convention does not arise.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 79, Proposition 5.6

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 79, Proposition 5.6: let I, I.1 and I.2 (with scalar `α`) hold.
(a) If `ε > 0`, `εᵢ > 0` with `∑_{k=0}^∞ α^k ε_k = ε`, and `π* = (μ₀*, μ₁*, …)` satisfies
`T_{μ_k*}(J*) ≤ T(J*) + ε_k` for all `k`, then `J* ≤ J_{π*} ≤ J* + ε`.
(b) If `ε > 0`, `α < 1` and `μ* ∈ M` satisfies `T_{μ*}(J*) ≤ T(J*) + ε(1 − α)`, then
`J* ≤ J_{μ*} ≤ J* + ε`. -/
theorem prop5_6_eps_optimal_from_bellman {S C : Type*} (m : MonotoneDP.Increase.Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (α : ℝ) (hI2 : m.AssumptionI2 α) :
    (∀ ε : ℝ, 0 < ε → ∀ εs : ℕ → ℝ, (∀ i, 0 < εs i) → HasSum (fun k => α ^ k * εs k) ε →
      ∀ π : m.Policy, (∀ k : ℕ, m.Tmu (π k) m.Jstar ≤ fun x => m.T m.Jstar x + (εs k : EReal)) →
        m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal)) ∧
    (∀ ε : ℝ, 0 < ε → α < 1 → ∀ μ : m.Selector,
      m.Tmu μ m.Jstar ≤ (fun x => m.T m.Jstar x + ((ε * (1 - α) : ℝ) : EReal)) →
        m.Jstar ≤ m.Jmu μ ∧ m.Jmu μ ≤ fun x => m.Jstar x + (ε : EReal)) := by sorry

end BertsekasShreve.Monotone
