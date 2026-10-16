-- Prove2me | Theorems.Thm_CustomerVoice_Payoffs_proposition_8_i
-- name    : CustomerVoice.Payoffs.proposition_8_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:08:01.035018+00:00
-- url     : https://prove2.me/theorems/fa235b8c-7f88-4ff3-831d-bf54ee82c60f
-- title:
--   Proposition 8(i), p. 23 — the seller's A-Learning payoff exceeds its O-Learning payoff
-- statement:
--   In the two-type customization model with $\theta_H>\theta_L>0$, $0<\alpha,\gamma<1$, and $k,s>0$, let $V^A$ and $V^O$ be the seller's expected payoffs evaluated at the A-Learning and O-Learning equilibrium qualities. Then
--   $$V^A>V^O.$$
--
--   This is the seller's gross-payoff comparison in Proposition 8.
--
--   **Formalization Note** The statement uses the printed payoff formulas for every model satisfying the standing assumptions. It does not add an equilibrium-existence threshold; pricing is represented by the paper's reduced-form payoff.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 23, Proposition 8(i)

import Mathlib
import Definitions.Def_CustomerVoice_Payoffs_Setting

namespace CustomerVoice.Payoffs

theorem proposition_8_i (M : Model) (hM : M.Standing) :
    M.VA > M.VO := by sorry

end CustomerVoice.Payoffs
