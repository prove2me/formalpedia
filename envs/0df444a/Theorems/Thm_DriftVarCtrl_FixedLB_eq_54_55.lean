-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_eq_54_55
-- name    : DriftVarCtrl.FixedLB.eq_54_55
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:15.600153+00:00
-- url     : https://prove2.me/theorems/5158d3fc-ee7e-4fe1-a2c8-6e8bc06db20f
-- title:
--   Proof of Theorem 2 (a), (52)–(55), p. EC-4 — the always-1 value is (54), and under (7) it satisfies the control-2 inequality (55)
-- statement:
--   Assume $v_1 < v_2$. The function
--   $$V(x) = -\frac{h_1}{\mu_1}x - \frac{M\mu_1 + h_1U}{\mu_1(1 - e^{-v_1U})}e^{-v_1x} + \frac{M\mu_1 + h_1U}{\mu_1(1 - e^{-v_1U})}$$
--   is the value of the static policy "always use control 1", i.e. it satisfies $V(0) = 0$, $V(U) = M$ (52) and $h_1 + \mu_1V'(x) + \frac{\sigma_1^2}{2}V''(x) = 0$ (53). Moreover, if condition (7) holds, then
--   $$h_2 + \mu_2V'(x) + \frac{\sigma_2^2}{2}V''(x) \ge 0\qquad\text{for all } x\in[0,U]. \tag{55}$$
--
--   Together with the verification lemma (Lemma 12) this proves part (a) of Theorem 2.
--
--   **Formalization Note.** "Value" is the mission's analytic value (`IsValue`): $C^1$ on $[0,U]$, the boundary values, and the ODE on the open piece $(0,U)$. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-4, proof of Theorem 2 (a), (52)–(55)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants

namespace DriftVarCtrl.FixedLB

/-- Proof of Theorem 2 (a), (52)–(55) (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-4). The explicit function (54) is the value of the
static policy "always use control 1" (it solves (52)–(53)), and if (7) holds it satisfies (55):
`h₂ + μ₂V′(x) + σ₂²/2·V″(x) ≥ 0` for all `x ∈ [0, U]`.

Formalization Note: the value is the analytic one (`IsValue`); the standing `v₁ < v₂` (p. 12) is the
hypothesis `hv`. -/
theorem eq_54_55 (p : Params) (hv : v p .one < v p .two) :
    IsValue p (static p .one) (V54 p) ∧
    (cond7 p → ∀ x ∈ Set.Icc 0 p.U,
      0 ≤ p.h₂ + p.μ₂ * deriv (V54 p) x + p.σ₂ ^ 2 / 2 * deriv (deriv (V54 p)) x) := by sorry

end DriftVarCtrl.FixedLB
