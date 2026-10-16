-- Prove2me | Theorems.Thm_CustomerVoice_Payoffs_proposition_8
-- name    : CustomerVoice.Payoffs.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:08:01.750999+00:00
-- url     : https://prove2.me/theorems/bfeab821-2f5a-4e1c-8da5-4b580cc1721e
-- title:
--   Proposition 8, p. 23 — seller and buyer payoff rankings and their fixed-cost reversals
-- statement:
--   Consider the paper's two-type customization model with $\theta_H>\theta_L>0$, $0<\alpha,\gamma<1$, and $k,s>0$. Let $V^A,V^O$ be the seller's expected gross payoffs and $U^A_i,U^O_i$ the type-$i$ buyer's gross payoffs at the A-Learning and O-Learning equilibrium qualities. Proposition 8 states four comparisons:
--
--   1. The seller receives more under A-Learning: $V^A>V^O$.
--   2. For every $F>0$, some $\tilde s_F>0$ makes $V^A(s)-F<V^O(s)$ for every $0<s<\tilde s_F$.
--   3. Each type receives more under O-Learning: $U^A_i<U^O_i$ for $i\in\{H,L\}$.
--   4. For every $G>0$ and each type $i$, some $\tilde s_{iG}>0$ makes $U^A_i(s)>U^O_i(s)-G$ for every $0<s<\tilde s_{iG}$.
--
--   The proposition compares gross benefits from the two design rights and explains when a positive incremental fixed cost reverses each preference.
--
--   **Formalization Note** In the small-$s$ clauses only $s$ changes, and each threshold is selected before the varying $s$. The statements hold for all parameters satisfying the section's standing assumptions without separately assuming the existence thresholds for both separating equilibria. The price stage is represented by the printed reduced-form payoffs, and the buyer payoffs retain their maxima with zero.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 23, Proposition 8

import Mathlib
import Definitions.Def_CustomerVoice_Payoffs_Setting

namespace CustomerVoice.Payoffs

theorem proposition_8 (M : Model) (hM : M.Standing) :
    M.VA > M.VO ∧
    (∀ F : ℝ, F > 0 → ∃ sF : ℝ, sF > 0 ∧
      ∀ s' : ℝ, 0 < s' → s' < sF →
        (M.withS s').VA - F < (M.withS s').VO) ∧
    (∀ t : CustomerVoice.ALearn.BType, M.UA t < M.UO t) ∧
    (∀ G : ℝ, G > 0 → ∀ t : CustomerVoice.ALearn.BType, ∃ sG : ℝ, sG > 0 ∧
      ∀ s' : ℝ, 0 < s' → s' < sG →
        (M.withS s').UA t > (M.withS s').UO t - G) := by sorry

end CustomerVoice.Payoffs
