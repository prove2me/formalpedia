-- Prove2me | Theorems.Thm_CustomerVoice_ONoOther_low_request_first_best
-- name    : CustomerVoice.ONoOther.low_request_first_best
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:41.555589+00:00
-- url     : https://prove2.me/theorems/2cc357f5-709c-4dfc-91c2-00959e4d1967
-- title:
--   Appendix, p. 28 — in case 1 every separating equilibrium has low request q*(θL)
-- statement:
--   Let the two-type O-Learning customization model satisfy $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, and $k,s>0$. If the type ratio obeys $\theta_H/\theta_L<\min\{\Lambda_{H1},\Lambda_{H2}\}$, then in every separating pure-strategy equilibrium, under any belief function consistent on path, the low type requests its complete-information optimum:
--   $$
--   q_L=q^*(\theta_L)=\min\left\{\frac{\gamma\theta_L}{s+\gamma k},\frac{\theta_L}{2k}\right\}.
--   $$
--   This pins down the low type's request in the first case of the Appendix's nonexistence argument.
--
--   **Formalization Note** The paper prints the ratio condition in this case. Requests and deviations are nonnegative; off-path beliefs remain arbitrary.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 28, Appendix, No Other Separating Equilibrium under the O-Learning Customization

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting

namespace CustomerVoice.ONoOther

theorem low_request_first_best (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < min M.LambdaH1 M.LambdaH2)
    (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType) (heq : M.OSepEq req bel) :
    req .L = M.qStar M.θL := by sorry

end CustomerVoice.ONoOther
