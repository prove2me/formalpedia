-- Prove2me | Theorems.Thm_AmbDiversify_Smooth_delta_const
-- name    : AmbDiversify.Smooth.delta_const
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:09.870919+00:00
-- url     : https://prove2.me/theorems/0947c761-16e0-4b1e-b9b8-b9b5761781bd
-- title:
--   Proof of Props 4.1–4.2, p. 16 (PDF 17) — if p1 = 1 − p2, then ∆(1) = ∆(2)
-- statement:
--   Let $u:\mathbb R\to\mathbb R$, $W_0,L\in\mathbb R$, and let the experts' probabilities satisfy $p_1 = 1-p_2$. Then the two experts assign the same value to diversification:
--
--   $$\Delta(1) = VD_{risk}(p_1) = VD_{risk}(p_2) = \Delta(2).$$
--
--   This is the observation that reduces case (i) of Proposition 4.1 to Lemma 1: every expert's utility rises by the same amount $\Delta$ under diversification.
--
--   **Formalization Note** No hypothesis on $u$ or on the range of $p_1,p_2$ is needed.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), p. 16 (PDF 17), proof of Propositions 4.1 and 4.2, 'Finally, if p1 = 1 − p2, …'

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

namespace AmbDiversify.Smooth

/-- Proof of Propositions 4.1 and 4.2, p. 16: if `p1 = 1 − p2`, the value of diversification is
the same for each expert, `∆(1) = ∆(2)`. -/
theorem delta_const (u : ℝ → ℝ) (W0 L p1 p2 : ℝ) (h : p1 = 1 - p2) :
    VD_risk u W0 L p1 = VD_risk u W0 L p2 := by sorry

end AmbDiversify.Smooth
