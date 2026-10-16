-- Prove2me | Theorems.Thm_CustomerVoice_ONoOther_high_mimics_low
-- name    : CustomerVoice.ONoOther.high_mimics_low
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:34.602028+00:00
-- url     : https://prove2.me/theorems/e542ed0c-a2ba-42cf-967a-6c9bbb5d94ea
-- title:
--   Appendix, pp. 28–29 — case 1 has no separating equilibrium
-- statement:
--   In the two-type O-Learning customization model with $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, and $k,s>0$, suppose
--   $$
--   \frac{\theta_H}{\theta_L}<\min\{\Lambda_{H1},\Lambda_{H2}\}.
--   $$
--   Then no pair of distinct nonnegative requests and no belief function consistent on path form a separating pure-strategy equilibrium. This is the Appendix's first failure case: the high type has an incentive to imitate the low type's request.
--
--   **Formalization Note** The statement ranges over every belief function; the price-setting stage is represented by the paper's reduced-form payoff.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), pp. 28–29, Appendix, No Other Separating Equilibrium under the O-Learning Customization

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting

namespace CustomerVoice.ONoOther

theorem high_mimics_low (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < min M.LambdaH1 M.LambdaH2) :
    ¬ ∃ (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType), M.OSepEq req bel := by sorry

end CustomerVoice.ONoOther
