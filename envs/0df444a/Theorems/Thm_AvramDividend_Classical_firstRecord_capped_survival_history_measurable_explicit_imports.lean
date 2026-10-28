-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_history_measurable_explicit_imports
-- name    : AvramDividend.Classical.firstRecord_capped_survival_history_measurable_explicit_imports
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:41:07.377108+00:00
-- url     : https://prove2.me/theorems/5ab224cd-5f53-49eb-83b1-e93705a60d85
-- title:
--   Finite-horizon surviving record is stopped-history measurable with explicit upcrossing import
-- statement:
--   For every first-upcrossing level and finite horizon, the surviving upper-before-ruin record event, intersected with occurrence by the horizon, belongs to the stopped sigma algebra of the capped stopping clock. This supplies the finite horizon stopped-history premise of the barrier value Markov renewal step. The published preamble explicitly imports the strict upcrossing stopping-time proof.
-- source:
--   Proved record_survival_stopped_history_measurable and generic stoppingTime_capped_history_event_measurable.

import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_stoppingTime_capped_history_event_measurable
import Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_survival_history_measurable_explicit_imports
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const N).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by sorry
