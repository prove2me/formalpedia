-- Prove2me | Theorems.Thm_ActuarialAnnuities_survival_whole_split
-- name    : ActuarialAnnuities.survival_whole_split
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:04:36.313249+00:00
-- url     : https://prove2.me/theorems/c5604485-1237-4459-8e24-7ea7731d3446
-- title:
--   Survival Whole Split
-- statement:
--   Whole-horizon annuity splits into temporary and deferred windows without guarantee.
--
--   Mathematical relation:
--
--   $$
--   V_{0:h}=V_{0:m}+V_{m:h}
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 157, Deferred annuities (Chapter 5, section 5.8). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV

namespace ActuarialAnnuities

theorem survival_whole_split (h m delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hm : m ≤ h) : bSurvivalPV h 0 h 0 delta v b p = bSurvivalPV h 0 m 0 delta v b p+bSurvivalPV h m (h-m) 0 delta v b p := by sorry

end ActuarialAnnuities
