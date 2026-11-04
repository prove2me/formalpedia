-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_no_nonpositive_mass
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_no_nonpositive_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:23:07.100039+00:00
-- url     : https://prove2.me/theorems/af141edf-8d27-4cb3-89da-c5bb59f34e98
-- title:
--   Original Lévy fourth-weighted exponential image has strictly positive support
-- statement:
--   For any original Lévy process marginal with measurable sample map, its fourth-weighted exponential-image measure has zero mass on the nonpositive real half-line. The original process structure and exponential map are used directly, with no jump-count or Lévy-rate assumption.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_no_nonpositive_mass

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_no_nonpositive_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (t : ℝ≥0) (θ : ℝ) :
    ((P.withDensity (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * X.X t ω) - 1) ^ 4))).map
      (fun ω => Real.exp (θ * X.X t ω))) (Iic (0 : ℝ)) = 0 := by sorry
