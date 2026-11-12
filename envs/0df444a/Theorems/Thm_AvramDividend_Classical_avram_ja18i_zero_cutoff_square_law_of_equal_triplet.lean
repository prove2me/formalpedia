-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18i_zero_cutoff_square_law_of_equal_triplet
-- name    : AvramDividend.Classical.avram_ja18i_zero_cutoff_square_law_of_equal_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:33:33.903236+00:00
-- url     : https://prove2.me/theorems/1ed8ffca-90e6-480c-bd4d-406114eac1ee
-- title:
--   Original zero-cutoff Gaussian quadratic residual has the same law under equal Lévy triplets
-- statement:
--   For two original spectrally negative Lévy processes, potentially on different spaces, with exactly equal drift, Gaussian coefficient and Lévy measure, the squared cutoff-zero physical intrinsic residual at any deterministic t has the same probability law. Use the proved universal Borel functional and whole-path Lévy law equality. This theorem transfers integrability to the original process once a finite-activity canonical comparison model is constructed.
-- source:
--   JA18 original Gaussian bracket distributional bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18i_universal_zero_cutoff_path_borel
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja18i_zero_cutoff_square_law_of_equal_triplet
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (t : ℝ≥0) :
    P₁.map (fun ω : Ω₁ => (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) =
      P₂.map (fun ω : Ω₂ => (avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω) ^ 2) := by sorry
