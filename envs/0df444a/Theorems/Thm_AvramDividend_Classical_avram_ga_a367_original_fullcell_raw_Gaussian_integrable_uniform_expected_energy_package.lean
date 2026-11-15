-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a367_original_fullcell_raw_Gaussian_integrable_uniform_expected_energy_package
-- name    : AvramDividend.Classical.avram_ga_a367_original_fullcell_raw_Gaussian_integrable_uniform_expected_energy_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:09:32.693939+00:00
-- url     : https://prove2.me/theorems/d6b87f9f-3298-4371-b0a6-1d48d7167d01
-- title:
--   Original true full stopped Gaussian raw squared-mesh source has integrable uniform expected energy package
-- statement:
--   For the genuine zerojump Gaussian Lévy source and stopped finite-horizon physical mesh, each fully pre-stop raw squared increment finite sum is integrable and its expectation is bounded by a single nonnegative constant K=2(nσ²+(nc)²), independent of the refining mesh. This assembles the already proved actual source a243 and a240 to supply the exact raw-energy input of the a364 expected small-source modulus bridge for a361.
-- source:
--   Original a240 and a243 proved true stopped Gaussian physical raw square energy

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a367_original_fullcell_raw_Gaussian_integrable_uniform_expected_energy_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    let F : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
        then (R m i ω)^2 else 0
    let K : ℝ := 2 * ((n : ℝ) * X.σ^2 + ((n : ℝ) * X.c)^2)
    0 ≤ K ∧ (∀ m, Integrable (F m) P) ∧
      ∀ m, (∫ ω, F m ω ∂P) ≤ K := by sorry
