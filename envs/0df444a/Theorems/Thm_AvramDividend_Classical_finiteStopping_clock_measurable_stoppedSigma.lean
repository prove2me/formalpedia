-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteStopping_clock_measurable_stoppedSigma
-- name    : AvramDividend.Classical.finiteStopping_clock_measurable_stoppedSigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:09:49.799453+00:00
-- url     : https://prove2.me/theorems/7b726fe4-39eb-44f8-b346-548eb444ff0f
-- title:
--   The finite stopping clock is measurable at its stopped-history sigma-algebra
-- statement:
--   Any finite stopping-time clock takes measurable values when the domain is equipped with the stopped-history sigma-algebra associated with its WithTop stopping-time lift. Prove measurability on the half-infinite closed intervals of the nonnegative real time axis; their inverse images are precisely the stopped-history clock-threshold events.
-- source:
--   Mathlib IsStoppingTime.measurableSet criterion and measurable_of_Iic, with proved threshold-event lemma f267fcd5-37e0-4c1e-aba2-2eaa671e7bbe; needed to deduce IndepFun clock/future Lévy path from strong-Markov independence of stopped sigma-algebra.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_finiteStopping_threshold_event_stoppedHistory
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.finiteStopping_clock_measurable_stoppedSigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    Measurable[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] τ := by
  sorry
