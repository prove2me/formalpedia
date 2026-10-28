-- Prove2me | Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
-- name    : AvramDividend.Classical.isStoppingTime_withTop_of_le_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:49:54.917979+00:00
-- url     : https://prove2.me/theorems/7851293c-fd3e-4bc8-b3cb-9653ccf13cf3
-- title:
--   Finite-valued stopping-time filtration condition implies Mathlib IsStoppingTime
-- statement:
--   The stopped-history convention used in the Lévy mission, that each event {τ≤s} belongs to filtration F_s, directly entails Mathlib's IsStoppingTime for the canonical WithTop coercion of finite nonnegative stopping times. This is needed to apply the proved bounded stopping-grid convergence result to the strong-Markov barrier stopping times.
-- source:
--   Exact type/interface bridge for open strong-Markov shifted-path independence 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and dividend-value barrier splitting child 79978d61-9d1f-4b20-b8a5-114797a8e380. Connects hτ to IsStoppingTime without W.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.isStoppingTime_withTop_of_le_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) := by
  sorry
