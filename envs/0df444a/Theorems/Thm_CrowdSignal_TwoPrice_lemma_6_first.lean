-- Prove2me | Theorems.Thm_CrowdSignal_TwoPrice_lemma_6_first
-- name    : CrowdSignal.TwoPrice.lemma_6_first
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:08.493542+00:00
-- url     : https://prove2.me/theorems/537b57a9-e2bd-43ec-a6fc-84b5928c8ef7
-- title:
--   Lemma 6, p. 26, first part — high-type full-information prices induce profitable imitation
-- statement:
--   Suppose $0<q_L<q_H\le(\alpha^2+6\alpha+25)q_L/16$, $0<\alpha<1$, and $0<T\le(3+\alpha)q_L/8$. The high type's full-information optimum from Lemma 4 is $((3+\alpha)q_H/8,q_H/2)$. If the low type imitates this pair while customers believe quality is high, his payoff exceeds his own full-information maximum:
--   $$\Pi^{LH}\bigl((3+\alpha)q_H/8,q_H/2\bigr)>\Pi^{L*}.$$
--   Thus the high type cannot separate by simply using his full-information prices.
--
--   **Formalization Note** This is the first sentence of Lemma 6. Its second sentence, concerning a binding constraint at a separating equilibrium, is handled within Proposition 2 for $T\le\dot P_1$. The added financing bound is disclosed because the corrected target uses it.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 26, Lemma 6, first sentence

import Mathlib
import Definitions.Def_CrowdSignal_TwoPrice_Setting

namespace CrowdSignal.TwoPrice

/-- The first sentence of Lemma 6, p. 26. -/
theorem lemma_6_first (P : Params) (hP : P.Standing)
    (hgap : P.qH ≤ (P.α ^ 2 + 6 * P.α + 25) * P.qL / 16)
    (hTL : P.T ≤ (3 + P.α) / 8 * P.qL) :
    optPayoff P P.qL P.qL <
      payoff P P.qL P.qH ((3 + P.α) / 8 * P.qH, P.qH / 2) := by sorry

end CrowdSignal.TwoPrice
