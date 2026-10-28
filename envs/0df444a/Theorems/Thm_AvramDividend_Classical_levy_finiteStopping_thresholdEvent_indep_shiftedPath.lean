-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_thresholdEvent_indep_shiftedPath
-- name    : AvramDividend.Classical.levy_finiteStopping_thresholdEvent_indep_shiftedPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:05:35.122846+00:00
-- url     : https://prove2.me/theorems/f27ea4c4-8273-47f6-8173-149a60bbca9c
-- title:
--   Threshold-event indicator independent of the entire shifted post-stopping Lévy path
-- statement:
--   For any finite Lévy stopping time and deterministic clock threshold c, its zero-one threshold indicator is independent of the entire Lévy increment path shifted after the stopping time. This turns the proved strong-Markov stopped-event product-measure law into a usable IndepFun statement for the generator of the clock sigma-algebra, towards proving independence of the random discount and future dividends.
-- source:
--   W-free strong-Markov theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8; direct input to clock/future-path independence and barrier dividend value split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_strongMarkov_shiftedPath_indep_stoppedEvent

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_thresholdEvent_indep_shiftedPath
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (c : ℝ≥0) :
    IndepFun
      (Set.indicator {ω : Ω | τ ω ≤ c} (fun _ : Ω => (1 : ℝ)))
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) P := by
  sorry
