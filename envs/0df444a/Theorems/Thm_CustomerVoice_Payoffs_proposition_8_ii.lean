-- Prove2me | Theorems.Thm_CustomerVoice_Payoffs_proposition_8_ii
-- name    : CustomerVoice.Payoffs.proposition_8_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:47.330456+00:00
-- url     : https://prove2.me/theorems/833ddd23-7a31-4b1f-89a2-8df0e13f5c5c
-- title:
--   Proposition 8(ii), p. 23 — a fixed seller cost reverses the payoff ranking when selling is cheap
-- statement:
--   Fix $\theta_H>\theta_L>0$, $0<\alpha,\gamma<1$, and $k>0$. For every seller-side incremental fixed cost $F>0$, there is a threshold $\tilde s_F>0$ such that every positive selling cost $s<\tilde s_F$ satisfies
--   $$V^A(s)-F<V^O(s).$$
--
--   Thus a fixed extra cost of A-Learning reverses the seller's gross-payoff ranking at sufficiently low selling cost.
--
--   **Formalization Note** Only $s$ varies; the threshold may depend on the other model primitives and $F$, and it is chosen before $s$. The statement does not add a separating-equilibrium existence condition. Pricing uses the paper's reduced-form payoffs.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 23, Proposition 8(ii)

import Mathlib
import Definitions.Def_CustomerVoice_Payoffs_Setting

namespace CustomerVoice.Payoffs

theorem proposition_8_ii (M : Model) (hM : M.Standing) :
    ∀ F : ℝ, F > 0 → ∃ sF : ℝ, sF > 0 ∧
      ∀ s' : ℝ, 0 < s' → s' < sF →
        (M.withS s').VA - F < (M.withS s').VO := by sorry

end CustomerVoice.Payoffs
