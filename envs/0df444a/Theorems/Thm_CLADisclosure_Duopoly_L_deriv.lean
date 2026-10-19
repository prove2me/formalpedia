-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_L_deriv
-- name    : CLADisclosure.Duopoly.L_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:59.468545+00:00
-- url     : https://prove2.me/theorems/e3f551f5-6e47-43b4-af18-4f75f6aa92ea
-- title:
--   Proof of Proposition 2, p. A7 — derivative of the ex ante profit integral
-- statement:
--   For $0<x<1$, define $L(x)=\int_x^1\int_x^{q_a}F(q_b)\,dq_b\,dF(q_a)$. Then
--
--   $$L'(x)=-F(x)\bigl[1-F(x)\bigr]<0.$$
--
--   Thus the profit expression in equation (7) strictly decreases as the disclosure threshold rises.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. A7 (PDF 50), proof of Proposition 2, L′(x) display

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- The derivative of the profit integral in the proof of Proposition 2, p. A7. -/
theorem L_deriv {F f : ℝ → ℝ} (hF : QualityDist F f)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (Lfun F f) (-(F x * (1 - F x))) x ∧
      -(F x * (1 - F x)) < 0 := by sorry

end CLADisclosure.Duopoly
