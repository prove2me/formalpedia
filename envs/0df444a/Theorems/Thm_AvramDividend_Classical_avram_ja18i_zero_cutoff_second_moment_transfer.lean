-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18i_zero_cutoff_second_moment_transfer
-- name    : AvramDividend.Classical.avram_ja18i_zero_cutoff_second_moment_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:56:39.307431+00:00
-- url     : https://prove2.me/theorems/ad5a78b0-f53f-4e9c-9ff2-cbd9e885ffeb
-- title:
--   Original zero-cutoff Gaussian second moment integral is determined by the Lévy triplet
-- statement:
--   For any two original spectrally negative Lévy processes on possibly distinct probability spaces with exactly matching drift, Gaussian coefficient, and Lévy measure, the integrals of squared physical cutoff-zero Gaussian residuals coincide. This uses proved equality of their quadratic residual laws and measure-theoretic change of variables, with no auxiliary same-space identification. Under nonintegrability the Bochner integrals agree by the usual convention, while an integrable canonical comparison process will supply the actual value.
-- source:
--   JA18 square-law pushforward-to-expectation bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18i_zero_cutoff_square_law_of_equal_triplet
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja18i_zero_cutoff_second_moment_transfer
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (t : ℝ≥0) :
    (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2 ∂P₁) =
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2 ∂P₂) := by sorry
