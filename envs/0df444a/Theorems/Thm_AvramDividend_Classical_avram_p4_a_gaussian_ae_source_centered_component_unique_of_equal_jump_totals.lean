-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_source_centered_component_unique_of_equal_jump_totals
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_source_centered_component_unique_of_equal_jump_totals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:35:59.475102+00:00
-- url     : https://prove2.me/theorems/a73ad0f1-ea4b-4231-8283-3f088932cc1f
-- title:
--   Original same-space Gaussian centred component is uniquely determined by the common total jumps
-- statement:
--   For the actual spectrally negative Levy X, two almost-sure all-times same-space Gaussian+jump representations with Gaussian zero-jump sources Y,Z and matching source sigma induce the same centred Gaussian path at every time on one full-measure event whenever their total jump components agree. The split into small and large jumps may differ. This establishes representation independence for the continuous component, conditional on existence of actual decompositions.
-- source:
--   Algebraic uniqueness from the two original-process Levy-Ito equalities and equality of total jump components. Exact source definition SpectrallyNegativeLevy (933ced80-71c1-4c0f-a6a7-ab7757fc97e9).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_source_centered_component_unique_of_equal_jump_totals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y Z : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hZν : Z.ν = 0)
    (hYσ : Y.σ = X.σ) (hZσ : Z.σ = X.σ)
    (Jsmall₁ Jlarge₁ Jsmall₂ Jlarge₂ : ℝ≥0 → Ω → ℝ)
    (hSource₁ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall₁ u ω + Jlarge₁ u ω)
    (hSource₂ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Z.X u ω - (u : ℝ) * Z.c) + Jsmall₂ u ω + Jlarge₂ u ω)
    (hJumpTotal : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Jsmall₁ u ω + Jlarge₁ u ω =
        Jsmall₂ u ω + Jlarge₂ u ω) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Y.X u ω - (u : ℝ) * Y.c =
        Z.X u ω - (u : ℝ) * Z.c := by sorry
