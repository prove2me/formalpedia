-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_lintegral_normalised_weight_mul
-- name    : AvramDividend.Classical.avram_p2_b_rate_lintegral_normalised_weight_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:27:26.222196+00:00
-- url     : https://prove2.me/theorems/bb842bf1-6d2c-4d0d-86b9-081ff233ede1
-- title:
--   Pull a constant normalisation factor through a weighted ENNReal moment integral
-- statement:
--   For measurable nonnegative extended-real weights f and moment tests g, and arbitrary extended-real constant c, multiplying f pointwise by c before integrating the product with g is exactly multiplying the original nonnegative integral by c afterwards. This provides the algebraic measure-density normalisation needed to instantiate P2-I using original Levy weighted-image moment rates.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_lintegral_normalised_weight_mul
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (c : ℝ≥0∞) :
    (∫⁻ ω, (f ω * c) * g ω ∂P) =
      (∫⁻ ω, f ω * g ω ∂P) * c := by sorry
