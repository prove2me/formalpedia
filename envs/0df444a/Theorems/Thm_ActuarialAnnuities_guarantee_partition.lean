-- Prove2me | Theorems.Thm_ActuarialAnnuities_guarantee_partition
-- name    : ActuarialAnnuities.guarantee_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:01:55.746584+00:00
-- url     : https://prove2.me/theorems/1ed92268-e22e-4b37-bc41-95b3f409e911
-- title:
--   Guarantee Partition
-- statement:
--   The guarantee and post-guarantee sums are disjoint and exhaustive.
--
--   Mathematical relation:
--
--   $$
--   V=V_{\text{guaranteed}}+V_{\text{post}}
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 159, Guaranteed annuities (Chapter 5, section 5.9). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bGuaranteedPV
import Definitions.Def_actuarial_bPostGuaranteePV

namespace ActuarialAnnuities

theorem guarantee_partition (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bSurvivalPV h a n g delta v b p = bGuaranteedPV h a n g delta v b p+bPostGuaranteePV h a n g delta v b p := by sorry

end ActuarialAnnuities
