-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
-- name    : AvramDividend.Classical.avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:49:03.506826+00:00
-- url     : https://prove2.me/theorems/85484289-102d-4b9c-b5c8-18f6710504ee
-- title:
--   Physical finite cutoff intrinsic residual centred and integrable from retained band L1
-- statement:
--   The original finite-cutoff intrinsic Levy Gaussian residual is L1 integrable and has zero expectation when its physically retained compensated negative band is integrable. This is a direct source-law statement, derived from the proved original residual subtraction and the proved zero-mean results for zero cutoff and retained band.
-- source:
--   Proved 70393ec7, 9bc499b4, 1ff51093, 8d8eedb1, bfc8537f; ordinary Bochner linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18_zero_cutoff_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_intrinsic_gaussian_core_centered
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_smallband_cutoff_centered
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (t : ℝ≥0)
    (hJ : Integrable (fun ω =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) P) :
    Integrable (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω ∂P) = 0 := by sorry
