-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_no_nonpositive_mass
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_no_nonpositive_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:04:16.824196+00:00
-- url     : https://prove2.me/theorems/a8b3e340-1e49-4785-897e-22e4a39a1448
-- title:
--   Fourth-weighted exponential image measure has no mass on the nonpositive real half-line
-- statement:
--   Any fourth-exponentially weighted image law obtained by pushing a real-measurable map through exp(theta Y) charges no nonpositive image values, because the real exponential is strictly positive. This gives the precise positive-support constraint needed for weighted image finite-measure moment tightness and negative-mark inversion.

import Mathlib
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_no_nonpositive_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (θ : ℝ) :
    ((μ.withDensity (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
      (fun ω => Real.exp (θ * Y ω))) (Iic (0 : ℝ)) = 0  := by sorry
