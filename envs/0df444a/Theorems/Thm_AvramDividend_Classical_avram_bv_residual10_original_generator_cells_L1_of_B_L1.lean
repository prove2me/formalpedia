-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_generator_cells_L1_of_B_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_generator_cells_L1_of_B_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:52:54.597966+00:00
-- url     : https://prove2.me/theorems/dc97c47d-021b-4ec0-a7b0-360ff6e4adc9
-- title:
--   Original BV generator-cell grid sums inherit L1 from compensated B without additional bounds
-- statement:
--   If the canonical original BV residual budget B is integrable and decomposes into generator-grid cells G plus the exact weighted compensation-grid correction, then G is integrable and B=G almost surely for each finite grid. The weighted correction disappears by original Levy pathwise bounded variation, so no separate generator-cell L1 estimate is needed inside the localised B-integrable route. Does not assert unconditional integrability of arbitrary stopped generator grids.
-- source:
--   AVRAM BV-RESIDUAL10 round 8, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_weighted_grid_residual_zero_ae

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_generator_cells_L1_of_B_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (A : ℕ → Ω → ℕ → ℝ)
    (B G : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      B n ω = G n ω +
        ∑ i ∈ Finset.range (n + 1),
          A n ω i * (R (u n i) - R (u n (i + 1))))
    (hBI : ∀ n, Integrable (B n) P) :
    ∀ n, Integrable (G n) P ∧ B n =ᵐ[P] G n := by sorry
