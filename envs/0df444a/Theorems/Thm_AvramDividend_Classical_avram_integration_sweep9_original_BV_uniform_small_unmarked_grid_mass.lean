-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_BV_uniform_small_unmarked_grid_mass
-- name    : AvramDividend.Classical.avram_integration_sweep9_original_BV_uniform_small_unmarked_grid_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:52:54.09669+00:00
-- url     : https://prove2.me/theorems/4d4c17fd-2a37-41f3-8486-2ac9cae8fa5e
-- title:
--   Uniform original BV negative-jump grid residual small after finite marking
-- statement:
--   For almost every original BV spectrally negative Levy path and each positive tolerance, there exists a finite set of marked original jump times such that every strictly monotone finite grid of cells avoiding the marks and ending before the horizon has total residual negative jump mass below the tolerance. This uniformity covers random stopped source grids.
-- source:
--   Directly imports Proved P3-F finite marked jump absolute tail 0b53d65a, original physical nonnegative left jump 561ccef5, and sweep8 uniform all-grids tail 64379a7f. This records a genuine helper-to-helper dependency, without asserting canonical P3 incorporation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_BV_finite_negative_times_tail
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep8_original_BV_uniform_pathwise_grid_jump_mass_tail
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep9_original_BV_uniform_small_unmarked_grid_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ marked : Finset ℝ≥0,
        ∀ (u : ℕ → ℝ≥0) (cells : Finset ℕ),
          StrictMono u →
          (∀ i ∈ cells, u (i + 1) ≤ T) →
          (∀ i ∈ cells, ∀ t ∈ marked,
            ¬ (u i < t ∧ t ≤ u (i + 1))) →
          let J : ℝ≥0 → ℝ := fun t =>
            ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0
          Finset.sum cells (fun i => J (u (i + 1)) - J (u i)) < ε := by sorry
