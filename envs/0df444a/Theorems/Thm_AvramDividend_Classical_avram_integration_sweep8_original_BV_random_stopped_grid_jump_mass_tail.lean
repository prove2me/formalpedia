-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep8_original_BV_random_stopped_grid_jump_mass_tail
-- name    : AvramDividend.Classical.avram_integration_sweep8_original_BV_random_stopped_grid_jump_mass_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:25:54.396824+00:00
-- url     : https://prove2.me/theorems/71b696ff-b261-4d78-a079-8bf12345fd11
-- title:
--   Original BV negative-jump exclusion for path-dependent stopped finite grids
-- statement:
--   Under almost surely strictly increasing random finite-grid times, finite-horizon bounds and marked source-negative-jump avoidance, the original physical X.X excluded-tail inequality holds almost surely on the random grid.
-- source:
--   Specialises the uniform full-measure original source theorem to random stopping grids, preserving the original physical jumps and finite-horizon upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep8_original_BV_uniform_pathwise_grid_jump_mass_tail
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep8_original_BV_random_stopped_grid_jump_mass_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (u : Ω → ℕ → ℝ≥0) (cells : Ω → Finset ℕ)
    (marked : Ω → Finset ℝ≥0)
    (hGrid : ∀ᵐ ω ∂P, StrictMono (u ω))
    (hBound : ∀ᵐ ω ∂P, ∀ i ∈ cells ω, u ω (i + 1) ≤ T)
    (hAvoid : ∀ᵐ ω ∂P, ∀ i ∈ cells ω, ∀ t ∈ marked ω,
      ¬ (u ω i < t ∧ t ≤ u ω (i + 1))) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0
      let j : ℝ≥0 → ℝ := fun t =>
        if 0 < t ∧ t ≤ T then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0
      Finset.sum (cells ω) (fun i => J (u ω (i + 1)) - J (u ω i)) ≤
        ∑' t : ℝ≥0, if t ∈ marked ω then 0 else j t := by sorry
