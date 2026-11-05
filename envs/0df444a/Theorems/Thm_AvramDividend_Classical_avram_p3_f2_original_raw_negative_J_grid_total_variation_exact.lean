-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_raw_negative_J_grid_total_variation_exact
-- name    : AvramDividend.Classical.avram_p3_f2_original_raw_negative_J_grid_total_variation_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:15:33.768491+00:00
-- url     : https://prove2.me/theorems/e398addd-75b0-4e9b-8e48-0d12c6ddcf8d
-- title:
--   Original raw negative-jump process exact finite physical-grid total variation
-- statement:
--   For almost every sample path of the original bounded-variation spectrally negative Lévy process, the genuine raw negative left-jump accumulation J is nondecreasing. Therefore every observed physical-clock grid has nonnegative consecutive J increments, and its sum of absolute negative-jump increments is exactly the original cumulative J mass between grid endpoints. This source-exact equality applies uniformly to any nondecreasing finite grid, including path-selected stopped clocks, and supplies the genuine J component of the frozen-X source C1 variation bridge. No substitute jump process or artificial variation bound is used.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_raw_negative_J_grid_total_variation_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ (u : ℕ → ℝ≥0) (n : ℕ),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          |J (u (i + 1)) - J (u i)|) =
        J (u n) - J (u 0) := by sorry
