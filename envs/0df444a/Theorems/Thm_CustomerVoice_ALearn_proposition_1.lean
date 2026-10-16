-- Prove2me | Theorems.Thm_CustomerVoice_ALearn_proposition_1
-- name    : CustomerVoice.ALearn.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:57.852329+00:00
-- url     : https://prove2.me/theorems/fe70f31a-c54c-4860-81dd-f02371d3c061
-- title:
--   Proposition 1, p. 12 — informative A-Learning equilibrium iff θH/θL ≥ Δ
-- statement:
--   Consider Guo's two-type A-Learning customization game with $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, and $k,s>0$. Buyers send costless messages, the seller chooses a nonnegative quality that maximizes its expected payoff given the message-induced belief, and each type chooses its best message. Informative communication means that the two types send different messages in a perfect Bayesian equilibrium.
--
--   Such an equilibrium exists if and only if
--   $$\frac{\theta_H}{\theta_L}\geq\Delta=\max\left\{\frac{\gamma[2s+(1+\gamma)k]}{(1-\gamma)(2s+\gamma k)},\frac{2s+\gamma k}{\gamma k}\right\}.$$
--
--   This characterizes when cheap talk can credibly reveal buyer preferences and support type-dependent customization.
--
--   **Formalization Note** The two-message game has on-path type-consistent beliefs, attained seller optimization over $q\geq0$, and buyer optimality against both messages. The price-setting stage is represented by equations (4)–(5). The weak boundary is included, as in Proposition 1.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 12, Proposition 1

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

namespace CustomerVoice.ALearn

/-- Proposition 1, p. 12: informative A-Learning communication exists exactly
above the printed heterogeneity threshold. -/
theorem proposition_1 (M : Model) (hM : M.Standing) :
    M.InformativeEq ↔ M.θH / M.θL ≥ M.Delta := by sorry

end CustomerVoice.ALearn
