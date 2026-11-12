-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18i_zero_cutoff_square_integrable_transfer
-- name    : AvramDividend.Classical.avram_ja18i_zero_cutoff_square_integrable_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:52:07.666205+00:00
-- url     : https://prove2.me/theorems/c5c5b935-7b84-4798-8685-50b70cfbbdf5
-- title:
--   Physical zero-cutoff quadratic integrability transfers across equal-triplet Lévy processes
-- statement:
--   Any original spectrally negative Lévy process X has an integrable squared zero-cutoff intrinsic Gaussian residual at a fixed time if a (possibly separate probability-space) spectrally negative Lévy process Y with the same triplet has integrable squared zero-cutoff residual. Use the proved equality of quadratic-residual distributions and measurable pushforward integrability. This isolates the remaining true obligation as construction or identification of a finite-moment comparison model.
-- source:
--   JA18 physical Gaussian moment transfer

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18i_zero_cutoff_square_law_of_equal_triplet
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja18i_zero_cutoff_square_integrable_transfer
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (t : ℝ≥0)
    (hY : Integrable (fun ω : Ω₂ => (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2) P₂) :
    Integrable (fun ω : Ω₁ => (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P₁ := by sorry
