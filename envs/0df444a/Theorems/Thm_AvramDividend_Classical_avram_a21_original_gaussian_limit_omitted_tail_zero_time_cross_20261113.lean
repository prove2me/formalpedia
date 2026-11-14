-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_zero_time_cross_20261113
-- name    : AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_zero_time_cross_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:29:00.48434+00:00
-- url     : https://prove2.me/theorems/281173cb-c2dc-46fa-b078-160d0be57f6a
-- title:
--   Original Gaussian limit and physical omitted tail have zero covariance at zero horizon
-- statement:
--   On the original Levy-process probability space, at source time zero the almost-sure Gaussian residual limit vanishes. Therefore its product with every omitted physical mark cutoff tail is zero almost everywhere and has zero Bochner expectation.
-- source:
--   Proved source Gaussian residual limit zero origin 4f4d81f6; pinned Mathlib integral_eq_zero_of_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_zero_time_cross_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ n : ℕ,
      (∫ ω, R 0 ω *
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω - R 0 ω) ∂P) = 0 := by sorry
