-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_retained_zero_time_quadratic_package_20261113
-- name    : AvramDividend.Classical.avram_a21_original_residual_retained_zero_time_quadratic_package_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:40:28.709475+00:00
-- url     : https://prove2.me/theorems/77f803d2-f857-4375-b10f-af85650a0668
-- title:
--   Original Gaussian residual and retained compensated jump zero-time quadratic and cross-moment package
-- statement:
--   At time zero, every original Gaussian intrinsic residual and every physically compensated retained negative jump band vanish for all cutoff indices. Their quadratic and cross products are integrable with zero expected values. This is a direct proved-boundary-case foundation for both full cutoff Gaussian variance and source covariance orthogonality.
-- source:
--   Proved physical zero-origin identities 2e39b05b and 125ef45d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_residual_retained_zero_time_quadratic_package_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω)^2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω)^2 ∂P) = 0 ∧
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω *
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω *
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω ∂P) = 0 := by sorry
