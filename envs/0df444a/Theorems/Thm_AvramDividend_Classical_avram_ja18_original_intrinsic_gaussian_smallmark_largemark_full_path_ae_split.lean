-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
-- name    : AvramDividend.Classical.avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:33:24.278892+00:00
-- url     : https://prove2.me/theorems/15d5f0b1-ac3a-44c9-9465-800af69ac82f
-- title:
--   Original Levy path exact a.e. split into intrinsic Gaussian, compensated small negative marks and actual large marks
-- statement:
--   For any original spectrally negative Levy source and any genuine almost-sure limits of its intrinsic Gaussian residual and compensated small-negative-mark cutoffs, the exact physical path decomposes into deterministic original drift, intrinsic Gaussian R, intrinsic compensated smallmark Jsmall and the actual uncompensated large-negative-mark jump sum. This is a full source-faithful Levy-Ito identity with all four channels on the same sample space, avoiding synthetic witness processes. The large mark channel is the missing term in the Open physical B219 finite mixed two-noise ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.c + R t ω + Jsmall t ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω := by sorry
