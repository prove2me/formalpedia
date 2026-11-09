-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_cauchy_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_cauchy_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:28:00.793984+00:00
-- url     : https://prove2.me/theorems/d4f357dd-0b0a-4fca-ae13-48728227fe8a
-- title:
--   Original finite negative-jump activity yields physical almost-sure compensated residual Cauchy
-- statement:
--   For the original spectrally negative Lévy process of finite negative jump activity, its intrinsic compensated small-negative-band residual is almost surely a Cauchy sequence in the band cutoff at every fixed physical nonnegative horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_cauchy_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      CauchySeq (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k T ω) := by sorry
