-- Prove2me | Theorems.Thm_ActuarialAnnuities_increase_first
-- name    : ActuarialAnnuities.increase_first
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:03:07.402833+00:00
-- url     : https://prove2.me/theorems/1cbc5b7b-f98b-43f7-953f-1ff60221587f
-- title:
--   Increase First
-- statement:
--   First increasing temporary benefit is one instalment unit.
--
--   Mathematical relation:
--
--   $$
--   b_a=1
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bIncreasing

namespace ActuarialAnnuities

theorem increase_first (a : ℕ) : bIncreasing a a = 1 := by sorry

end ActuarialAnnuities
