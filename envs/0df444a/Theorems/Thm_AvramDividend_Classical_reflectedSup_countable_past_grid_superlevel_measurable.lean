-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_countable_past_grid_superlevel_measurable
-- name    : AvramDividend.Classical.reflectedSup_countable_past_grid_superlevel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:34:33.844622+00:00
-- url     : https://prove2.me/theorems/2b9d2fa4-eafa-4193-8db7-db084b654f3d
-- title:
--   Crossing a positive drawdown level on any countable deterministic observation schedule before time t is measurable by filtration t
-- statement:
--   For an adapted actual reflected spectrally negative Lévy process R, any countable deterministic observation schedule clock(n) bounded by horizon t, and any real level x, the event that R crosses or reaches x at one of those observation times is measurable in the filtration at t. Each observation event belongs to the sigma-algebra at its time by adaptedness, hence belongs to the sigma-algebra at t by filtration monotonicity, and the union is measurable. This provides the countable-grid event prerequisite for approximating genuine excursion-level first-passage times.
-- source:
--   Pinned Mathlib measurableSet_iUnion, Measurable.mono and Adapted for reflected SNLP, theorem reflectedSup_adapted.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.Process.Adapted
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_countable_past_grid_superlevel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (t : ℝ≥0)
    (hclock : ∀ n : ℕ, clock n ≤ t) (x : ℝ) :
    MeasurableSet[𝓕 t]
      {ω : Ω | ∃ n : ℕ, x ≤ reflectedSup X (clock n) ω} := by sorry
