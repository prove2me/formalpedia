-- Prove2me | Theorems.Thm_CrowdSignal_TwoPrice_dot_pair_maximizes_W
-- name    : CrowdSignal.TwoPrice.dot_pair_maximizes_W
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:06.588862+00:00
-- url     : https://prove2.me/theorems/deae4b59-b519-4f72-909d-49883a34ea8a
-- title:
--   Proof of Proposition 2, p. 41 — the dotted pair uniquely maximizes W on the iso-profit curve
-- statement:
--   Under the standing assumptions and the corrected small-gap regime, let $(\dot P_1,\dot P_2)$ satisfy $\dot P_2>q_H/2$, $4\dot P_1+(1-\alpha)\dot P_2=2q_H$, and $W^{LH}(\dot P_1,\dot P_2)=\Pi^{L*}$. On the iso-profit curve $W^{LH}(P_1,P_2)=\Pi^{L*}$ with $P_1<q_H$, the high type's printed objective $W^H$ has a unique maximizer:
--   $$W^H(P_1,P_2)\le W^H(\dot P_1,\dot P_2),$$
--   with equality only at $(P_1,P_2)=(\dot P_1,\dot P_2)$.
--
--   This isolates the constrained optimization assertion in the proof of Proposition 2, before applying the equilibrium constraints.
--
--   **Formalization Note** The curve uses the manuscript's $W^{LH}$ and $W^H$ expressions, and $P_1<q_H$ keeps their denominator $1-P_1/q_H$ nonzero. The added financing bound is the disclosed correction to the small-gap regime.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 41, Proof of Proposition 2, (A.13)–(A.15)

import Mathlib
import Definitions.Def_CrowdSignal_TwoPrice_Setting

namespace CrowdSignal.TwoPrice

/-- Proof of Proposition 2, p. 41, equations (A.13)–(A.14). -/
theorem dot_pair_maximizes_W (P : Params) (hP : P.Standing)
    (hgap : P.qH ≤ (P.α ^ 2 + 6 * P.α + 25) * P.qL / 16)
    (hTL : P.T ≤ (3 + P.α) / 8 * P.qL)
    (Pd : ℝ × ℝ) (h2 : P.qH / 2 < Pd.2)
    (hline : 4 * Pd.1 + (1 - P.α) * Pd.2 = 2 * P.qH)
    (hW : W P P.qL P.qH Pd.1 Pd.2 = optPayoff P P.qL P.qL) :
    IsGreatest ((fun x : ℝ × ℝ => W P P.qH P.qH x.1 x.2) ''
      {x | x.1 < P.qH ∧ W P P.qL P.qH x.1 x.2 = optPayoff P P.qL P.qL})
      (W P P.qH P.qH Pd.1 Pd.2) ∧
    (∀ x : ℝ × ℝ, x.1 < P.qH →
      W P P.qL P.qH x.1 x.2 = optPayoff P P.qL P.qL →
      W P P.qH P.qH x.1 x.2 = W P P.qH P.qH Pd.1 Pd.2 → x = Pd) := by sorry

end CrowdSignal.TwoPrice
