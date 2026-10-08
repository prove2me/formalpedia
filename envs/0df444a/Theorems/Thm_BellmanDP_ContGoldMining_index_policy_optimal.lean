-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_index_policy_optimal
-- name    : BellmanDP.ContGoldMining.index_policy_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T17:16:01.736457+00:00
-- url     : https://prove2.me/theorems/c04c9dbe-e35a-4c08-ae23-c5e90413370a
-- title:
--   Chapter VIII, Theorem 1 — the index rule maximizes $f(\infty)$ in the continuous two-mine process
-- statement:
--   Two mines A and B contain $x_0 \ge 0$ and $y_0 \ge 0$ units of gold. A single machine is divided between them: at time $t$ a proportion $\varphi_1(t) \in [0, 1]$ of effort goes to A and $\varphi_2(t) = 1 - \varphi_1(t)$ to B, with $\varphi_1$ measurable. The process is governed by Eq. (7.2):
--   $$\frac{dx}{dt} = -\varphi_1 r_1 x,\quad \frac{dy}{dt} = -\varphi_2 r_2 y,\quad \frac{dp}{dt} = -p(\varphi_1 q_1 + \varphi_2 q_2),\quad \frac{df}{dt} = p(\varphi_1 r_1 x + \varphi_2 r_2 y),$$
--   with $x(0) = x_0$, $y(0) = y_0$, $p(0) = 1$, $f(0) = 0$. Here $x, y$ are the gold remaining, $p$ is the probability that the machine still works, $f$ the expected gold mined, and $q_1, q_2, r_1, r_2 > 0$ are the failure and mining rates.
--
--   **Theorem.** Consider the feedback rule
--   $$\varphi_1 = 1 \text{ if } q_1 r_2 y < q_2 r_1 x,\qquad \varphi_2 = 1 \text{ if } q_1 r_2 y > q_2 r_1 x,\qquad \varphi_1 = \frac{r_2}{r_1 + r_2},\ \varphi_2 = \frac{r_1}{r_1 + r_2} \text{ if } q_1 r_2 y = q_2 r_1 x.$$
--   There is an admissible control that follows this rule along its own trajectory for almost every $t \ge 0$, and every such control maximizes the expected total gold $f(\infty)$ over all admissible controls.
--
--   The rule mines the mine with the larger index $r_1 x/q_1$ versus $r_2 y/q_2$, and on the line where the indices are equal it mixes in the proportions that keep the state on the line. It is the continuous analogue of the index rule for the discrete gold-mining process of Chapter II.
--
--   **Formalization Note** The process is defined by the closed-form solution of (7.2): with $\Phi_1(t) = \int_0^t \varphi_1$ and $\Phi_2(t) = t - \Phi_1(t)$, $x = x_0 e^{-r_1\Phi_1}$, $y = y_0 e^{-r_2\Phi_2}$, $p = e^{-q_1\Phi_1 - q_2\Phi_2}$. The maximization is over open-loop measurable controls $\varphi_1$ with values in $[0,1]$, as in the book; the feedback rule is realized as the class of open-loop controls consistent with it along their own trajectory, and the existence conjunct rules out a vacuous statement. $f(\infty)$ is a lower Lebesgue integral in $[0, \infty]$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, Theorem 1, p. 231 (process: § 7, Eqs. (7.2)-(7.3), p. 228)

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process

namespace BellmanDP.ContGoldMining

/-- Bellman, *Dynamic Programming*, Ch. VIII, Theorem 1, p. 231: for the two-choice process
(7.2) under the constraints (7.3), the maximum of `f(∞)` is attained by the policy
`φ₁ = 1` for `q₁ r₂ y < q₂ r₁ x`, `φ₂ = 1` for `q₁ r₂ y > q₂ r₁ x`, and
`φ₁ = r₂/(r₁ + r₂)`, `φ₂ = r₁/(r₁ + r₂)` for `q₁ r₂ y = q₂ r₁ x`.
Stated as: an admissible control following this feedback rule along its own trajectory exists,
and every such control maximizes `f(∞)` over all admissible controls. -/
theorem index_policy_optimal (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    (∃ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ ∧ FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁) ∧
    ∀ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ → FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁ →
      ∀ ψ₁ : ℝ → ℝ, TwoAdmissible ψ₁ →
        goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice ψ₁) ≤
          goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) := by sorry

end BellmanDP.ContGoldMining
