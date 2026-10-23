-- Prove2me | Theorems.Thm_CustomerVoice_ONoOther_no_other_separating
-- name    : CustomerVoice.ONoOther.no_other_separating
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:45.372092+00:00
-- url     : https://prove2.me/theorems/ef7c1fa4-5698-4d11-94c1-845c31947ded
-- title:
--   §3.3, p. 19 (Appendix, pp. 28–29) — no separating equilibrium exists when θH/θL < Λ
-- statement:
--   Let the two-type O-Learning customization model satisfy $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, and $k,s>0$. Define
--   $$
--   \Lambda=\max\left\{\min\left(\frac{\gamma(s+k)}{(1-\gamma)s},\frac{1+\gamma}{1-\gamma}\right),\frac{s}{\gamma k}\right\}.
--   $$
--   If $\theta_H/\theta_L<\Lambda$, there is no separating pure-strategy equilibrium: no pair of distinct nonnegative requests and no belief function on all requests, consistent at those requests, can make both buyer types optimal against every nonnegative deviation.
--
--   This is the nonexistence statement established by the two cases in the paper's Appendix.
--
--   **Formalization Note** Section 3.3 calls the cheap-signaling equilibrium “the only separating equilibrium,” but its Appendix establishes nonexistence below $\Lambda$; the stronger global uniqueness reading is false and is not asserted. Seller acceptance follows the printed inequality and accepts at equality. The pricing stage is reduced to equation (9), with zero payoff upon rejection.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 19, §3.3, after Proposition 4; pp. 28–29, Appendix, No Other Separating Equilibrium under the O-Learning Customization

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting

namespace CustomerVoice.ONoOther

theorem no_other_separating (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < M.Lambda) :
    ¬ ∃ (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType), M.OSepEq req bel := by sorry

end CustomerVoice.ONoOther
