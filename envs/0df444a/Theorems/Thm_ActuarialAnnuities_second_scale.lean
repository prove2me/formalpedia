-- Prove2me | Theorems.Thm_ActuarialAnnuities_second_scale
-- name    : ActuarialAnnuities.second_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:06:21.747988+00:00
-- url     : https://prove2.me/theorems/198a878f-a11b-4d9a-85e6-850962cd53f3
-- title:
--   Second Scale
-- statement:
--   Pathwise squares make the second moment quadratic in benefit scale.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[(cZ)^2]=c^2\mathbb E[Z^2]
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSecondMoment

namespace ActuarialAnnuities

theorem second_scale (h a n g delta : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : bSecondMoment h a n g delta v (fun j => c*b j) p = c^2*bSecondMoment h a n g delta v b p := by sorry

end ActuarialAnnuities
