-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a397_original_fullcell_gaussian_uniform_quadratic_integrable_majorant
-- name    : AvramDividend.Classical.avram_ga_a397_original_fullcell_gaussian_uniform_quadratic_integrable_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:50:38.444314+00:00
-- url     : https://prove2.me/theorems/82c2a3a7-e243-443f-a550-220669eb9d99
-- title:
--   Gaussian finite-horizon full-cell increments have a mesh-independent integrable quadratic envelope
-- statement:
--   The absolute centred full-cell Gaussian increment, its square and the mesh width share a common integrable random dominating variable uniformly over all physical meshes and their cells on a fixed horizon.
-- source:
--   Gaussian finite-horizon Brownian absolute running-supremum quadratic maximal moment and zero-jump continuous sample paths.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a397_original_fullcell_gaussian_uniform_quadratic_integrable_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0) (n : ℕ) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, 0 ≤ B ω) ∧
      (∀ (m : ℕ), ∀ᵐ ω ∂P, ∀ i : ℕ, i < m →
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        |z| + z^2 + (Δ : ℝ) ≤ B ω) := by sorry
