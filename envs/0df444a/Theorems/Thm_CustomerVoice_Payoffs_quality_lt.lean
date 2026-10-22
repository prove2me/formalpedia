-- Prove2me | Theorems.Thm_CustomerVoice_Payoffs_quality_lt
-- name    : CustomerVoice.Payoffs.quality_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:54.098599+00:00
-- url     : https://prove2.me/theorems/d974d520-2ea2-486b-930e-a70d3fc1fc08
-- title:
--   §3.4, pp. 21–22 — A-Learning quality is strictly below O-Learning quality
-- statement:
--   In the two-type customization model, suppose $\theta_H>\theta_L>0$, $0<\alpha,\gamma<1$, and $k,s>0$. For each buyer type $i\in\{H,L\}$, the equilibrium qualities satisfy
--   $$q^A_i<q^O_i.$$
--
--   The strict quality gap compares seller-designed and buyer-requested products and is the quality comparison used in Proposition 8.
--
--   **Formalization Note** The result compares the printed closed-form equilibrium qualities. The reduced-form pricing stage enters through the definitions of those qualities and payoffs.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), pp. 21–22, §3.4, opening quality comparison

import Mathlib
import Definitions.Def_CustomerVoice_Payoffs_Setting

namespace CustomerVoice.Payoffs

theorem quality_lt (M : Model) (hM : M.Standing) :
    ∀ t : CustomerVoice.ALearn.BType, M.qA t < M.qO t := by sorry

end CustomerVoice.Payoffs
