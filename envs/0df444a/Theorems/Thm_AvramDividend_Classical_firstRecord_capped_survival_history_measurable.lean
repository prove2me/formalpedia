-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_history_measurable
-- name    : AvramDividend.Classical.firstRecord_capped_survival_history_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:38:53.292189+00:00
-- url     : https://prove2.me/theorems/b07ab70d-a915-4059-9bfb-1f440a2f865f
-- title:
--   Survival to a strict record before a finite horizon is measurable in its stopped history
-- statement:
--   For every first-upcrossing level and finite horizon, the surviving upper-before-ruin record event, intersected with occurrence by the horizon, belongs to the stopped sigma algebra of the capped stopping clock. This supplies the finite horizon stopped-history premise of the barrier value Markov renewal step.
-- source:
--   Proved record_survival_stopped_history_measurable and generic stoppingTime_capped_history_event_measurable.

import Theorems.Thm_AvramDividend_Classical_stoppingTime_capped_history_event_measurable
import Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_survival_history_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const N).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by sorry
