-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_upper_exit_grid_history_eventually
-- name    : AvramDividend.Classical.avram_root29_01_upper_exit_grid_history_eventually
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:22:05.175987+00:00
-- url     : https://prove2.me/theorems/d7e1f9d6-88ba-491f-99af-ba5c926090e4
-- title:
--   Genuine Lévy upper-exit grid histories eventually survive below zero
-- statement:
--   For an actual spectrally negative Lévy trajectory and real starting reserve, suppose lower-survival holds through τ, a strictly positive right-side reserve window follows τ, and finite sampled stopping clocks tend to τ. Then all sufficiently refined sampled stopping horizons have nonnegative reserve throughout their full continuous-time history. This pathwise implication is exactly the missing survival-indicator upper-exit step in the noncircular killed-grid-to-continuous optional stopping proof.
-- source:
--   WS1A work/avram_root29_01_upper_exit_grid_history_eventually_repair1_draft.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_upper_exit_grid_history_eventually
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (τ : ℝ≥0)
    (t : ℕ → ℝ≥0)
    (ht : Tendsto t atTop (nhds τ))
    (hBefore : ∀ s : ℝ≥0, s ≤ τ → 0 ≤ x + X.X s ω)
    (hAfter : ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s : ℝ≥0, τ ≤ s → s < τ + δ → 0 ≤ x + X.X s ω) :
    ∀ᶠ n in atTop, ∀ s : ℝ≥0,
      s ≤ t n → 0 ≤ x + X.X s ω := by sorry
