-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys64_original_all_grid_BV_weighted_raw_residual_zero_ae
-- name    : AvramDividend.Classical.avram_bvb_phys64_original_all_grid_BV_weighted_raw_residual_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:19:06.450582+00:00
-- url     : https://prove2.me/theorems/afd88828-b0da-4be3-9123-24f66c377c30
-- title:
--   Original BV removed-jump residual contributes zero on every weighted physical grid
-- statement:
--   For the original bounded-variation Lévy process satisfying Standing, its canonical removed-jump residual is zero at every time almost surely. Hence for any deterministic triangular grid and any pathwise real weights, the entire signed weighted residual-difference sum vanishes almost surely. This removes the second term in the physical B generator grid used in 6ce6d0c3, with no stochastic approximation or auxiliary process.
-- source:
--   Original physical BV B residual simplification from Proved 79a63ca0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys64_original_all_grid_BV_weighted_raw_residual_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (W : ℕ → Ω → ℕ → ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∑ i ∈ Finset.range (n + 1),
        W n ω i * (R (u n i) - R (u n (i + 1))) = 0 := by sorry
