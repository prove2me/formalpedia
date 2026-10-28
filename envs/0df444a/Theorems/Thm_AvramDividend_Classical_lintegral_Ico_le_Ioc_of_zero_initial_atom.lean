-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_Ico_le_Ioc_of_zero_initial_atom
-- name    : AvramDividend.Classical.lintegral_Ico_le_Ioc_of_zero_initial_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:52:43.639362+00:00
-- url     : https://prove2.me/theorems/f37b93ae-2050-4674-a2bc-84f17c8e58fe
-- title:
--   A zero initial atom lets open-right reward windows dominate closed-left prefixes
-- statement:
--   For any nonnegative Stieltjes reward density and measure with no atom at zero, its integral over [0,t) is at most its integral over (0,t]. The set [0,t) lies in (0,t] union {0}; use monotonicity and subadditivity of set integrals and the null singleton. Needed to combine rational-prefix exhaustion with finite-horizon dividend estimates.
-- source:
--   Use lintegral_mono_set for [0,t) subset (0,t] union {0}, lintegral_union_le, and setLIntegral_measure_zero.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.lintegral_Ico_le_Ioc_of_zero_initial_atom
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ)
    (hzero : μ ({0} : Set ℝ) = 0) :
    (∫⁻ r in Ico (0 : ℝ) t, f r ∂μ) ≤
      (∫⁻ r in Ioc (0 : ℝ) t, f r ∂μ) := by sorry
