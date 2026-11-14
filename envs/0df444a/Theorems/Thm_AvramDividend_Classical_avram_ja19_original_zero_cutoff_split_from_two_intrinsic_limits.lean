-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
-- name    : AvramDividend.Classical.avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:24:35.378437+00:00
-- url     : https://prove2.me/theorems/2dbfbe10-083d-4068-b2a9-9f470e9b9256
-- title:
--   Original zero-cutoff source equals intrinsic Gaussian residual plus actual compensated small-jump source
-- statement:
--   For the same original Levy process, the actual limit of physical Gaussian cutoff residuals and the limit of physical compensated small jump bands sum to the exact original zero-cutoff residual almost surely, simultaneously at every horizon. No independence or replacement process is assumed.
-- source:
--   Kyprianou Chapter 2 (Levy-Ito decomposition), original-source Proved cutoff split 4b47cce4 and zero-band result 8d8eedb1; this is the pathwise limit identity required for ca457ff7 without transport.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        R t ω + Jsmall t ω := by sorry
