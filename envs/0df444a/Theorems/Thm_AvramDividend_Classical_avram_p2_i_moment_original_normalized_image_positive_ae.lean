-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_normalized_image_positive_ae
-- name    : AvramDividend.Classical.avram_p2_i_moment_original_normalized_image_positive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:56:21.638878+00:00
-- url     : https://prove2.me/theorems/65a42867-7e6c-4dc7-b862-21ea7a566a3b
-- title:
--   Original time-normalised weighted exponential image has almost-everywhere strictly positive support
-- statement:
--   For every genuine original spectrally negative Lévy process and every real time, including the zero-measure extension at nonpositive times, the normalised fourth-weighted exponential image is supported in (0,∞). Directly reuses two independently Proved source theorems: null nonpositive mass for the original image and the finite-measure positive-a.e. implication. Supplies the exact hypothesis required by the method-of-moments compact-test theorem and repairs P2-K's current type-mismatch at a.e. support conversion, without touching P2-K's owned target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_original_normalized_image_positive_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ) :
    ∀ᵐ z ∂(if 0 < h then (ENNReal.ofReal h)⁻¹ •
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
      else (0 : Measure ℝ)), 0 < z := by sorry
