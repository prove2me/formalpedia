-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_paymentTimes_Ioi_integral_eq_positive_weight
-- name    : AvramDividend.Classical.avram_root29_05_paymentTimes_Ioi_integral_eq_positive_weight
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:57:35.011893+00:00
-- url     : https://prove2.me/theorems/a3d770cd-be9b-43b3-8c15-d185efc5d5df
-- title:
--   Original stopped positive-time Stieltjes integral equals indicator-form reward
-- statement:
--   For any measure on real times, arbitrary killed payment-time clock and nonnegative weight, integrating over the intersection of strictly positive times and paymentTimes equals integrating over paymentTimes with an explicit positive-time weight indicator. This identifies the exact two interfaces used in the source barrier dividend value and sampled reconstruction.
-- source:
--   Use Mathlib lintegral_indicator for the positive half-line and restrict-restrict measure intersection symmetry; this is a purely measure-theoretic identity, independent of any Lévy path or Markov assumption.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal Classical

/-- Intersecting the true stopped payment set with positive real times is
equivalent to the same positive-time indicator on the stopped Stieltjes reward. -/

theorem AvramDividend.Classical.avram_root29_05_paymentTimes_Ioi_integral_eq_positive_weight
    (μ : Measure ℝ) (τ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioi (0 : ℝ) ∩ paymentTimes τ, w r ∂μ) =
    (∫⁻ r in paymentTimes τ, if 0 < r then w r else 0 ∂μ) := by sorry
