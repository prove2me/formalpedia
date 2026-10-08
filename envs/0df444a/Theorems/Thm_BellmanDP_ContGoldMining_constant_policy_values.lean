-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_constant_policy_values
-- name    : BellmanDP.ContGoldMining.constant_policy_values
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T17:15:48.507395+00:00
-- url     : https://prove2.me/theorems/703c4027-0a1c-44bb-86a2-e8601ba77f7d
-- title:
--   Chapter VIII, Eq. (10.1) — $f_A(\infty) = r_1x_0/(q_1+r_1)$ and $f_B(\infty) = r_2y_0/(q_2+r_2)$
-- statement:
--   Consider the continuous two-choice gold-mining process with failure rates $q_1, q_2 > 0$, mining rates $r_1, r_2 > 0$ and initial amounts $x_0, y_0 \ge 0$ of gold in mines A and B. If mine A is worked for all $t \ge 0$ ($\varphi_1 \equiv 1$, $\varphi_2 \equiv 0$), then $x(t) = x_0 e^{-r_1 t}$, $y(t) = y_0$, $p(t) = e^{-q_1 t}$, and the expected total gold is
--   $$f_A(\infty) = \frac{r_1 x_0}{q_1 + r_1}.$$
--   If mine B is worked for all $t \ge 0$ ($\varphi_1 \equiv 0$, $\varphi_2 \equiv 1$), the expected total gold is
--   $$f_B(\infty) = \frac{r_2 y_0}{q_2 + r_2}.$$
--
--   Bellman uses the comparison of these two values to show that mine B is used near the $y$-axis, which is the first step towards Theorem 1.
--
--   **Formalization Note** $f(\infty)$ is an extended nonnegative real (lower Lebesgue integral), so both identities are stated with `ENNReal.ofReal` of the right-hand side.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 10, Eq. (10.1), pp. 230-231

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process

namespace BellmanDP.ContGoldMining

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 10, Eq. (10.1), pp. 230–231: using `A` for all
`t ≥ 0` yields `f_A(∞) = r₁ x₀/(q₁ + r₁)`, and using `B` for all `t ≥ 0` yields
`f_B(∞) = r₂ y₀/(q₂ + r₂)`. -/
theorem constant_policy_values (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice fun _ => 1) =
        ENNReal.ofReal (r₁ * x₀ / (q₁ + r₁)) ∧
      goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice fun _ => 0) =
        ENNReal.ofReal (r₂ * y₀ / (q₂ + r₂)) := by sorry

end BellmanDP.ContGoldMining
