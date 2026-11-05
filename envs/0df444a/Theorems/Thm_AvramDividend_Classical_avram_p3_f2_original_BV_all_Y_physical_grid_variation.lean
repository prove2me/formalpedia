-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_BV_all_Y_physical_grid_variation
-- name    : AvramDividend.Classical.avram_p3_f2_original_BV_all_Y_physical_grid_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:49:54.269201+00:00
-- url     : https://prove2.me/theorems/26250e74-0a1e-4cb5-8b80-e748e7bde5d0
-- title:
--   Uniform original BV jump-removed Y absolute variation over every physical finite clock grid from actual drift and monotone residual
-- statement:
--   For almost every original bounded-variation spectrally negative Lévy sample path, the genuine raw negative jump series J and nondecreasing source residual R=t drift-X-J give the exact identity Y=X+J=t drift-R. For every nondecreasing finite physical grid, the absolute increment of Y is bounded by absolute drift times the clock increment plus the nonnegative R increment. Sum and telescope to bound the entire original absolute Y variation by |drift| times elapsed real physical time plus the exact source R increment. The almost sure event is uniform over all grids, including path-selected clocks; no assumed finite-variation envelope or abstract substitute path is used.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_BV_all_Y_physical_grid_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (u : ℕ → ℝ≥0) (n : ℕ),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          |Y (u (i + 1)) - Y (u i)|) ≤
        |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
          (R (u n) - R (u 0)) := by sorry
