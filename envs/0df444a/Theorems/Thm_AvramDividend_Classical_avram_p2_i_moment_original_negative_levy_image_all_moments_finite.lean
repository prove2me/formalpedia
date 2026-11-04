-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_levy_image_all_moments_finite
-- name    : AvramDividend.Classical.avram_p2_i_moment_original_negative_levy_image_all_moments_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:57:29.499383+00:00
-- url     : https://prove2.me/theorems/347d9768-1994-4d21-82e7-eeebe391a4dd
-- title:
--   Every moment of the actual negative Lévy fourth-weighted exponential image is finite
-- statement:
--   The genuine spectrally negative Lévy fourth-weighted negative-jump exponential image has finite ENNReal moments of every natural degree. Its source-proved finite total mass and compact [0,1] support feed the P2-I universal moment domination theorem. Supplies P2-K's limit moment finiteness exactly, avoiding a fragile lower-integral power-bridge conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_original_negative_levy_image_all_moments_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp)) ≠ ⊤ := by sorry
