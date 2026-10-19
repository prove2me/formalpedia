-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_two_interval_value
-- name    : DriftVarCtrl.FixedLB.two_interval_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:10.895253+00:00
-- url     : https://prove2.me/theorems/756a17fe-dadc-4fea-bf3d-55ac597915ff
-- title:
--   (73)–(75) with (87), pp. EC-8, EC-11 — V₁₂(x; S) is the value of the policy 'control 1 on [0, S), control 2 on [S, U)'
-- statement:
--   For every switching point $S \in (0,U)$, the function $V_{12}(\cdot\,;S)$, equal to
--   $$V_{0S}(x) = -\frac{h_1}{\mu_1}x + A_1(e^{-v_1x} - 1)\quad (x \le S),\qquad V_{SU}(x) = -\frac{h_2}{\mu_2}x + \frac{M\mu_2 + h_2U}{\mu_2} + A_3(e^{-v_2x} - e^{-v_2U})\quad (x > S),$$
--   with $A_3 = A_3(S,h_2)$ given by (87) and $A_1$ by (75), is the value of the two-interval policy that uses control 1 on $[0,S)$ and control 2 on $[S,U)$: it is continuously differentiable on $[0,U]$, vanishes at $0$, equals $M$ at $U$, and solves
--   $$h_1 + \mu_1V' + \frac{\sigma_1^2}{2}V'' = 0 \text{ on } (0,S),\qquad h_2 + \mu_2V' + \frac{\sigma_2^2}{2}V'' = 0 \text{ on } (S,U).$$
--
--   This identifies the closed form used in Lemmas 4–10 with the value of the "1 then 2" policy.
--
--   **Formalization Note.** The printed (73) shows $\sigma_1^2/2$ in the second equation; the equation for control 2 has $\sigma_2^2/2$ ((59)), and (74) solves that one. The value is the mission's analytic value (`IsValue`).
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-8, (73)–(75), and p. EC-11, (87)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_TwoInterval

namespace DriftVarCtrl.FixedLB

/-- Proof of Lemma 4, (73)–(75) with (87) (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. EC-8 and EC-11). For every switching point
`S ∈ (0, U)`, the function `V₁₂(·; S)` built from (74) with `A₃` from (87) and `A₁` from (75) is the value
of the two-interval policy "control 1 on `[0, S)`, control 2 on `[S, U)`".

Formalization Note: the printed (73) has `σ₁²/2` in the control-2 equation; it is `σ₂²/2` ((59)), and
(74) is its solution. The value is the analytic one (`IsValue`); no ordering of `v₁, v₂` is needed. -/
theorem two_interval_value (p : Params) :
    ∀ (S : ℝ) (hS : S ∈ Set.Ioo 0 p.U), IsValue p (twoInt p .one S hS) (V12 p S p.h₂) := by sorry

end DriftVarCtrl.FixedLB
