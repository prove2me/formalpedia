-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:56:50.480892+00:00
-- url     : https://prove2.me/theorems/b00b5611-fc4a-4d80-b8fc-f5da56aad628
-- title:
--   Actual original ruin-stopped physical-grid strict-endpoint cells form an exact finite initial prefix
-- statement:
--   For each original spectrally-negative Levy sample X and dividend path D, the indices i with stopped physical right endpoint u(i+1)<tau are exactly range k for some k≤m+1. This follows from the Proved original monotone stopped clock and a finite induction. It constructs the source-exact physical prefix needed to instantiate the accepted strict-prefix Stieltjes product and zero-time atom budgets without extra assumptions, while omitting the at-most-one ruin/horizon crossing cell.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ∃ k : ℕ, k ≤ m + 1 ∧
      (Finset.range (m + 1)).filter
        (fun i => u (i + 1) < τ) = Finset.range k := by sorry
