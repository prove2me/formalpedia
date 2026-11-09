-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:18:24.425056+00:00
-- url     : https://prove2.me/theorems/e9bcbe6c-ebb7-4b40-9128-dad38f3387e5
-- title:
--   Original finite-activity empty negative annulus bounds intrinsic Gaussian residual increment
-- statement:
--   If an original-process physical negative-jump annulus has zero marked mass, the corresponding change in the original intrinsic compensated Gaussian residual is bounded by physical horizon multiplied by strip width and the finite total negative-jump intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_strip
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (hnm : n ≤ m) (T : ℝ≥0) (ω : Ω)
    (hVoid :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioc (-(1 / ((n : ℝ) + 1)))
          (-(1 / ((m : ℝ) + 1)))) = 0) :
    |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| ≤
      (T : ℝ) * ((1 / ((n : ℝ) + 1)) *
        (X.ν (Iio (0 : ℝ))).toReal) := by sorry
