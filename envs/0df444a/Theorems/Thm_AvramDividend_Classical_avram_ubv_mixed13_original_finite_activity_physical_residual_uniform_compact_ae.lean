-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_uniform_compact_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_uniform_compact_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:33:22.263206+00:00
-- url     : https://prove2.me/theorems/25322807-ba1e-4474-bdfd-52b9414516ac
-- title:
--   Original finite-activity compensated residual converges uniformly on bounded physical horizons
-- statement:
--   At almost every sample path of an original finite-negative-activity spectrally negative Lévy process, compensated small-negative-band residual increments are uniformly small over every fixed bounded physical time interval, in particular at bounded random stopping clocks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_uniform_compact_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m →
        ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
          |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
             avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| < η := by sorry
