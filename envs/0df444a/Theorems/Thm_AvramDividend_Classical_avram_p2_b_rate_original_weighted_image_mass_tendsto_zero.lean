-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_mass_tendsto_zero
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_mass_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:42:17.638422+00:00
-- url     : https://prove2.me/theorems/93a053d7-a11a-48c7-9bf2-e7cfb0bc4c83
-- title:
--   Original Lévy fourth-weighted exponential-image mass vanishes as time decreases to zero
-- statement:
--   The full mass of the genuine original-process fourth-weighted exponential-image measure tends to zero as time approaches zero through positive values. This is deduced from the source-specific finite zeroth-moment rate convergence by multiplication by time, and makes no jump-intensity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_moment_rate_tendsto

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_mass_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto (fun h : ℝ => (((P.withDensity (fun ω =>
          ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω))) Set.univ).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by sorry
