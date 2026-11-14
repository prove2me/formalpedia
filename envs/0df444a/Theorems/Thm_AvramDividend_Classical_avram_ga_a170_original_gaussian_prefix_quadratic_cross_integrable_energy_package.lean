-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
-- name    : AvramDividend.Classical.avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:41:50.728195+00:00
-- url     : https://prove2.me/theorems/e1d3bee1-e772-4aab-83b9-1cb62de3108b
-- title:
--   Original stopped Gaussian source prefix quadratic raw-centred cross integrability and bounded expected energy
-- statement:
--   The exact original Gaussian source with zero Levy measure and true stopped prefix uniform grid has integrable centred square-energy, expected centred energy at most horizon n times Gaussian volatility squared, and integrable absolute raw-versus-centred quadratic cross at each mesh. This supplies the three exact premises needed for the already proved generic ga_a81 L1 vanishing, which then bounds the fully pre-stop source ga_a169.
-- source:
--   Proved ga37/ga39 original stopped second-energy, X.isProbability, original stopped mask measurability, finite Gaussian second moment and ga85 square cross bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    let A : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          |(Z m i ω + (Δ m : ℝ) * X.c)^2 - (Z m i ω)^2|
        else 0
    let E : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then (Z m i ω)^2 else 0
    (∀ m : ℕ, Integrable (A m) P) ∧
    (∀ m : ℕ, Integrable (E m) P) ∧
    (∀ m : ℕ, (∫ ω, E m ω ∂P) ≤ (n : ℝ) * X.σ^2) := by sorry
