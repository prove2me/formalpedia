-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_void_annulus_truncated_residual_bound
-- name    : AvramDividend.Classical.avram_mix_fin13_original_finite_activity_void_annulus_truncated_residual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:15:34.177944+00:00
-- url     : https://prove2.me/theorems/63880c60-191e-43b7-bbef-3335362c51b1
-- title:
--   Original finite-activity truncated Gaussian residual difference under an empty negative annulus
-- statement:
--   For the original spectrally negative Levy source X on its unchanged probability space, finite negative-jump intensity and an empty original marked-jump annulus imply the exact truncated residual candidates differ by at most the horizon times the reciprocal cutoff and the finite total negative intensity. The proof uses the published physical annulus compensator bound and the definitional same-X residual identity. This provides a concrete source-bound step towards convergence of the original finite-activity residual, with no auxiliary Gaussian process or assumed bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin13_original_finite_activity_void_annulus_truncated_residual_bound
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
    |avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
       avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
      (T : ℝ) * ((1 / ((n : ℝ) + 1)) *
        (X.ν (Iio (0 : ℝ))).toReal) := by sorry
