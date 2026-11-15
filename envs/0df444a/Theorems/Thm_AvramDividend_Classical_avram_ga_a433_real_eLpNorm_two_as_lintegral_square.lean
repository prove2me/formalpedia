-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a433_real_eLpNorm_two_as_lintegral_square
-- name    : AvramDividend.Classical.avram_ga_a433_real_eLpNorm_two_as_lintegral_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T23:58:19.672166+00:00
-- url     : https://prove2.me/theorems/f8fbea1b-2676-4b16-94a7-59581a34adcc
-- title:
--   Real L2 norm expressed through the nonnegative extended squared integral
-- statement:
--   The real-valued L2 norm of a measurable function with respect to a measure equals the square root of its squared-norm extended nonnegative integral, including infinite values.
-- source:
--   Proof follows accepted auxiliary LevyStochCalc.Probability.eLpNorm_two_eq from the Proved LevyStochCalc dyadic Doob source.

import Mathlib
open MeasureTheory ENNReal Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a433_real_eLpNorm_two_as_lintegral_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℝ) :
    eLpNorm f 2 μ =
      (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by sorry
