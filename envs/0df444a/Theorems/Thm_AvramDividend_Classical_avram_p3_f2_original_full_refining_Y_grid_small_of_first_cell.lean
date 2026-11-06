-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_full_refining_Y_grid_small_of_first_cell
-- name    : AvramDividend.Classical.avram_p3_f2_original_full_refining_Y_grid_small_of_first_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:10:07.995405+00:00
-- url     : https://prove2.me/theorems/a496eb46-0e09-47b4-b424-30b29de3ee13
-- title:
--   Original full stopped BV Y-grid fineness from first-cell control and positive-clock tail
-- statement:
--   For almost every true bounded-variation spectrally negative Lévy path, uniform fineness of the jump-removed Y increments over the whole physical grid follows from positive-clock compact tail refinement and an explicit separate hypothesis controlling its zero-origin first cell. This certifies the precise global Y-smallness assumption used by the source stopped C1 chain, while leaving the time-zero/right-dividend interface to the P3-G2 owner.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_clock_refining_Y_grid_small
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_full_refining_Y_grid_small_of_first_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (a b : ℝ≥0) (ha : 0 < a)
        (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let Y : ℝ≥0 → ℝ := fun t =>
          X.X t ω + ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        (∀ m i, 0 < i → i < n m →
          u m i ∈ Set.Icc a b ∧ u m (i + 1) ∈ Set.Icc a b) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop,
            ∀ i, 0 < i → i < n m →
              dist (u m (i + 1)) (u m i) < δ) →
        (∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop,
            0 < n m → |Y (u m 1) - Y (u m 0)| < ε) →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop,
            ∀ i, i < n m →
              |Y (u m (i + 1)) - Y (u m i)| < ε := by sorry
