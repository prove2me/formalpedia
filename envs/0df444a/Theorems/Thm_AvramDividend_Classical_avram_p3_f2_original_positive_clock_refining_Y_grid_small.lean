-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_clock_refining_Y_grid_small
-- name    : AvramDividend.Classical.avram_p3_f2_original_positive_clock_refining_Y_grid_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:18:47.207255+00:00
-- url     : https://prove2.me/theorems/25acaa0b-7710-4231-80c9-1637109fde28
-- title:
--   Original positive-clock time refinement yields eventually small actual BV jump-removed Y cells
-- statement:
--   On one full-measure event of the genuine original bounded-variation Lévy process, its jump-removed physical source Y is uniformly continuous on any strictly positive compact clock interval. Consequently every sequence of finite physical grids contained in that interval whose adjacent real-clock distances vanish eventually has uniformly vanishing source Y increments across all cells. This proves the actual source-increment fineness premise needed for a discounted refining-mesh C1 limit. The time-zero cell must be handled by the separately owned P3-G2 zero/right-jump decomposition.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_positive_clock_refining_Y_grid_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (a b : ℝ≥0) (ha : 0 < a)
        (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let Y : ℝ≥0 → ℝ := fun t =>
          X.X t ω + ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        (∀ m i, i < n m →
          u m i ∈ Set.Icc a b ∧ u m (i + 1) ∈ Set.Icc a b) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop,
            ∀ i, i < n m → dist (u m (i + 1)) (u m i) < δ) →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop,
            ∀ i, i < n m →
              |Y (u m (i + 1)) - Y (u m i)| < ε := by sorry
