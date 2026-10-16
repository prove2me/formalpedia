-- Prove2me | Theorems.Thm_CrowdSignal_TwoPrice_dot_pair_unique
-- name    : CrowdSignal.TwoPrice.dot_pair_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:14.822554+00:00
-- url     : https://prove2.me/theorems/b61173ff-67de-4344-9125-7e9d3042e7eb
-- title:
--   Proof of Proposition 2, p. 41 — uniqueness of the dotted pricing pair
-- statement:
--   Suppose $0<q_L<q_H\le(\alpha^2+6\alpha+25)q_L/16$, $0<\alpha<1$, and $0<T\le(3+\alpha)q_L/8$. Let $\Pi^{L*}$ be the maximum two-period payoff of a low-quality entrepreneur believed low. There is exactly one committed price pair $(\dot P_1,\dot P_2)$ satisfying
--   $$\dot P_2>q_H/2,\qquad 4\dot P_1+(1-\alpha)\dot P_2=2q_H,\qquad W^{LH}(\dot P_1,\dot P_2)=\Pi^{L*}.$$
--   This identifies the pair used in Proposition 2 without choosing a root by convention.
--
--   **Formalization Note** The added financing bound $T\le(3+\alpha)q_L/8$ is needed for the corrected small-gap result; Proposition 2 omits it in print. $W^{LH}$ is the manuscript's displayed rational expression. This theorem states uniqueness of the system's solution; Proposition 2 separately assumes its funding price covers $T$.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 41, Proof of Proposition 2, after (A.15)

import Mathlib
import Definitions.Def_CrowdSignal_TwoPrice_Setting

namespace CrowdSignal.TwoPrice

/-- Proof of Proposition 2, p. 41: the dotted pair solves the system uniquely. -/
theorem dot_pair_unique (P : Params) (hP : P.Standing)
    (hgap : P.qH ≤ (P.α ^ 2 + 6 * P.α + 25) * P.qL / 16)
    (hTL : P.T ≤ (3 + P.α) / 8 * P.qL) :
    ∃! x : ℝ × ℝ, P.qH / 2 < x.2 ∧
      4 * x.1 + (1 - P.α) * x.2 = 2 * P.qH ∧
      W P P.qL P.qH x.1 x.2 = optPayoff P P.qL P.qL := by sorry

end CrowdSignal.TwoPrice
