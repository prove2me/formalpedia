-- Prove2me | Theorems.Thm_CustomerVoice_Payoffs_proposition_8_iii
-- name    : CustomerVoice.Payoffs.proposition_8_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:53.19958+00:00
-- url     : https://prove2.me/theorems/bf8fc076-e8d6-45df-be55-be754c21e128
-- title:
--   Proposition 8(iii), p. 23 — each buyer type earns more under O-Learning
-- statement:
--   In the two-type customization model with $\theta_H>\theta_L>0$, $0<\alpha,\gamma<1$, and $k,s>0$, let $U^A_i$ and $U^O_i$ be the type-$i$ buyer payoffs from the A-Learning and O-Learning equilibrium qualities. For both $i=H$ and $i=L$,
--   $$U^A_i<U^O_i.$$
--
--   This is the buyers' gross-payoff comparison in Proposition 8.
--
--   **Formalization Note** Both buyer payoffs are evaluated through the paper's equations (5) and (9), including their maxima with zero. No equilibrium-existence threshold is added; pricing is in reduced form.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 23, Proposition 8(iii)

import Mathlib
import Definitions.Def_CustomerVoice_Payoffs_Setting

namespace CustomerVoice.Payoffs

theorem proposition_8_iii (M : Model) (hM : M.Standing) :
    ∀ t : CustomerVoice.ALearn.BType, M.UA t < M.UO t := by sorry

end CustomerVoice.Payoffs
