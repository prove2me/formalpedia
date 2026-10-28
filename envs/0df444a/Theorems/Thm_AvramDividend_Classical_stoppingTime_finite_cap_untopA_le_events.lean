-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppingTime_finite_cap_untopA_le_events
-- name    : AvramDividend.Classical.stoppingTime_finite_cap_untopA_le_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:27:34.256872+00:00
-- url     : https://prove2.me/theorems/68cd3feb-ae91-4459-a56b-1fbd22df8b21
-- title:
--   Extracting a finite NNReal stopping clock from a capped WithTop stopping time
-- statement:
--   If T is a possibly infinite stopping time, the finite-valued random clock obtained by first capping it at a finite horizon N and then applying WithTop.untopA has observable at-or-before events in each filtration sigma-algebra. This is the exact finite-clock input required for the existing right-continuous strong Markov factorisation.
-- source:
--   Mathlib IsStoppingTime.min_const, WithTop.untopA_le_iff, ne_top_of_le_ne_top.

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stoppingTime_finite_cap_untopA_le_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTime 𝓕 τ) (N : ℝ≥0) :
    ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
      {ω : Ω | (min (τ ω) (N : ℝ≥0∞)).untopA ≤ s} := by sorry
