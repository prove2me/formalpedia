-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finiteactivity_gaussian_plus_smalljump_second_moment_corrected
-- name    : AvramDividend.Classical.avram_ja21_original_finiteactivity_gaussian_plus_smalljump_second_moment_corrected
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T14:27:47.864475+00:00
-- url     : https://prove2.me/theorems/6b5b767b-47c8-4e39-bcee-7a7ce78b7cbf
-- title:
--   Correct finite-activity original intrinsic cutoff-zero quadratic moment includes compensated small-jump variance
-- statement:
--   At cutoff zero the small-band Ioc(-1,-1) is empty, while original truncated residual subtracts drift c and actual large-mark sum over (-infinity,-1]. Its quadratic moment includes Gaussian variance sigma squared plus compensated small-jump quadratic variance, t times the y squared Levy integral over (-1,0). This corrects b12c5163. Example sigma=1, intensity one Poisson jumps of size -1/2, compensated in the Levy triplet: E[residual(0,1)^2]=5/4, whereas b12c5163 asserts 1. Preserve the original X and finite negative activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_finiteactivity_gaussian_plus_smalljump_second_moment_corrected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ^ 2 ∂P) = (t : ℝ) * (X.σ ^ 2 +
        ∫ y in Ioo (-1 : ℝ) (0 : ℝ), y ^ 2 ∂X.ν) := by sorry
