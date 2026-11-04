-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_kmoment_finite
-- name    : AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_kmoment_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:10:41.731243+00:00
-- url     : https://prove2.me/theorems/bf2f2528-35cc-4840-acb4-0d12ba9b7620
-- title:
--   Every kth moment of the original positive-time normalised fourth-weighted exponential image is finite
-- statement:
--   For any actual original spectrally negative Lévy process X, positive real time h and degree k, the ENNReal kth moment of its inverse-h-normalised fourth-weighted exp(X_h) image measure is finite; no compensated jump count assumptions.
-- source:
--   For positive real h, use the original adaptedness to build the measurable exp(X_h) image. The weighted pushforward kth ENNReal moment equals the actual original-space weighted source moment by lintegral_map and the withDensity identity. Source theorem 52a535dd supplies its finiteness at every k, using exp(X_h)>0 for ofReal_pow. Scaling by inverse positive h preserves a finite ENNReal moment. This closes a necessary explicit P2-I hypothesis without assuming a jump-rate or compensator.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_polynomial_moments_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_kmoment_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
      ((ENNReal.ofReal h)⁻¹ •
        ((P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (X.X (Real.toNNReal h) ω))))) < ⊤ := by sorry
