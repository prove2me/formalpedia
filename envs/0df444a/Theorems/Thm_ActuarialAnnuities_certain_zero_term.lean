-- Prove2me | Theorems.Thm_ActuarialAnnuities_certain_zero_term
-- name    : ActuarialAnnuities.certain_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:04:14.403009+00:00
-- url     : https://prove2.me/theorems/bb42bd4b-802a-409f-8421-02ef355ebbe5
-- title:
--   Certain Zero Term
-- statement:
--   The annuity-certain comparison also has an empty-term boundary.
--
--   Mathematical relation:
--
--   $$
--   n=0\Longrightarrow V_{\text{certain}}=0
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 157, Deferred annuities (Chapter 5, section 5.8). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bCertainPV

namespace ActuarialAnnuities

theorem certain_zero_term (h a delta : ℕ) (v : ℝ) (b : ℕ → ℝ) : bCertainPV h a 0 delta v b = 0 := by sorry

end ActuarialAnnuities
