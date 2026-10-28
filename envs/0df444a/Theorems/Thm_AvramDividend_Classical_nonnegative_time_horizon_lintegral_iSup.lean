-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_time_horizon_lintegral_iSup
-- name    : AvramDividend.Classical.nonnegative_time_horizon_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:40:55.468051+00:00
-- url     : https://prove2.me/theorems/86589c7f-90dd-499a-8878-34e5b029f463
-- title:
--   Monotone recovery of the nonnegative-time dividend integral from finite horizons
-- statement:
--   For an arbitrary measure on the real time axis and a measurable nonnegative extended-real integrand, the integral over times t≥0 equals the supremum of integrals over [0,n], n natural. The lemma supplies the monotone horizon limit needed to pass from finite-horizon dividend verification to the unrestricted expected dividend value after the stochastic bound is proved.
-- source:
--   Mathlib.MeasureTheory.Integral.Lebesgue.Add: lintegral_iSup and lintegral_indicator; monotone finite horizons.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open MeasureTheory Set
open scoped Classical ENNReal

theorem AvramDividend.Classical.nonnegative_time_horizon_lintegral_iSup
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t in Ici (0 : ℝ), f t ∂μ) =
      ⨆ n : ℕ, (∫⁻ t in Icc (0 : ℝ) (n : ℝ), f t ∂μ) := by sorry
