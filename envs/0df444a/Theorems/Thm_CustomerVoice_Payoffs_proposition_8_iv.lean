-- Prove2me | Theorems.Thm_CustomerVoice_Payoffs_proposition_8_iv
-- name    : CustomerVoice.Payoffs.proposition_8_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:57.769149+00:00
-- url     : https://prove2.me/theorems/7a8feece-5524-4278-abfb-cec64ff4bd0c
-- title:
--   Proposition 8(iv), p. 23 — a fixed buyer cost reverses each type's payoff ranking when selling is cheap
-- statement:
--   Fix $\theta_H>\theta_L>0$, $0<\alpha,\gamma<1$, and $k>0$. For every buyer-side incremental fixed cost $G>0$ and every type $i\in\{H,L\}$, there is a threshold $\tilde s_{iG}>0$ such that every positive selling cost $s<\tilde s_{iG}$ satisfies
--   $$U^A_i(s)>U^O_i(s)-G.$$
--
--   Thus each type's extra fixed cost of O-Learning reverses its gross-payoff ranking at sufficiently low selling cost.
--
--   **Formalization Note** Only $s$ varies; the threshold may depend on the buyer type, the other primitives, and $G$, and it is chosen before $s$. The statement does not add a separating-equilibrium existence condition. Pricing uses the paper's reduced-form payoffs.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 23, Proposition 8(iv)

import Mathlib
import Definitions.Def_CustomerVoice_Payoffs_Setting

namespace CustomerVoice.Payoffs

theorem proposition_8_iv (M : Model) (hM : M.Standing) :
    ∀ G : ℝ, G > 0 → ∀ t : CustomerVoice.ALearn.BType, ∃ sG : ℝ, sG > 0 ∧
      ∀ s' : ℝ, 0 < s' → s' < sG →
        (M.withS s').UA t > (M.withS s').UO t - G := by sorry

end CustomerVoice.Payoffs
