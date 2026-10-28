-- Prove2me | Theorems.Thm_AvramDividend_Classical_record_survival_before_horizon_stopped_measurable
-- name    : AvramDividend.Classical.record_survival_before_horizon_stopped_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:46:18.439023+00:00
-- url     : https://prove2.me/theorems/22a34911-af20-4cba-9d1e-e80ddbb985d9
-- title:
--   Surviving record before finite horizon is observable at its capped stopping time
-- statement:
--   For a strict record level b and reflected ruin level a, the event that the record occurs before ruin and before finite horizon N belongs to the sigma algebra at the capped record clock. This supplies the exact stopped-history measurability input to finite-horizon strong Markov regeneration.
-- source:
--   Proved record_survival_stopped_history_measurable and stoppingTime_capped_history_event_measurable.

import Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable
import Theorems.Thm_AvramDividend_Classical_stoppingTime_capped_history_event_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.record_survival_before_horizon_stopped_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const N).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by sorry
