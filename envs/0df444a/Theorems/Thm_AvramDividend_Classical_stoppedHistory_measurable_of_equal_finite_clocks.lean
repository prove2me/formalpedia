-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedHistory_measurable_of_equal_finite_clocks
-- name    : AvramDividend.Classical.stoppedHistory_measurable_of_equal_finite_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:51:30.31499+00:00
-- url     : https://prove2.me/theorems/15c19b45-e4af-4df6-a147-29c3f9e5bab1
-- title:
--   Stopped-history measurability transports across pointwise equal finite and extended clocks
-- statement:
--   If a finite nonnegative stopping-time clock and an extended-valued stopping-time clock agree pointwise after coercion, then every event measurable at the extended stopped-history sigma algebra is measurable at the finite-clock stopped-history sigma algebra. This removes a representation mismatch in the finite-horizon Lévy first-record strong Markov argument.
-- source:
--   Definition of Mathlib IsStoppingTime.measurableSpace and proved isStoppingTime_withTop_of_le_events; function extensionality and proof irrelevance.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stoppedHistory_measurable_of_equal_finite_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (T : Ω → ℝ≥0∞) (hT : IsStoppingTime 𝓕 T)
    (hEq : ∀ ω : Ω, (τ ω : ℝ≥0∞) = T ω)
    (A : Set Ω) (hA : MeasurableSet[hT.measurableSpace] A) :
    MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A := by sorry
