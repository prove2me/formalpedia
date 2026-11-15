-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a40_original_zero_nu_intrinsic_gaussian_normalised_exact_law_20261114
-- name    : AvramDividend.Classical.avram_a40_original_zero_nu_intrinsic_gaussian_normalised_exact_law_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:23:19.498421+00:00
-- url     : https://prove2.me/theorems/dac7110c-3a9f-4c9d-b14c-2598cf21843f
-- title:
--   Original zero-jump intrinsic Gaussian cutoff residual normalized by sigma has exact centred normal marginals
-- statement:
--   If the actual original spectrally negative Lévy process has no negative jumps and has positive Gaussian volatility, then any intrinsic Gaussian cutoff limit R has, after normalization by sigma, precisely the centred Gaussian law with variance t at each deterministic time on the same original probability measure.
-- source:
--   Proved A22 original zero-nu intrinsic cutoff same-source companion; Proved gbB264 exact original zerojump normalized Gaussian increment law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
import Theorems.Thm_AvramDividend_Classical_avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a40_original_zero_nu_intrinsic_gaussian_normalised_exact_law_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hNu : X.ν = 0) (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ t : ℝ≥0,
      Measure.map (fun ω => R t ω / X.σ) P = gaussianReal 0 t := by sorry
