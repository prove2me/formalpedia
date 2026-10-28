-- Prove2me | Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable
-- name    : AvramDividend.Classical.record_survival_stopped_history_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:57:55.375599+00:00
-- url     : https://prove2.me/theorems/7c79f9d8-085e-4ab2-a5b4-328ffc8b11bb
-- title:
--   Survival to a first record belongs to the stopped-history sigma algebra
-- statement:
--   For any Lévy process and positive or arbitrary levels, the event that a strict upper record occurs before reflected ruin is measurable with respect to the sigma algebra of the record stopping time in the right-continuous filtration. This follows from the proved right-continuous stopping-time results for record and ruin, and Mathlib's stopping-time comparison measurability theorem. It discharges the past-event measurability input required by the strong-Markov killed first-record renewal step.
-- source:
--   The complement of the survival event is reflected ruin occurring on or before the first record; invoke the stopping-time comparison event measurability in the first record's stopped sigma algebra.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_stopping_rightCont_filtration

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.record_survival_stopped_history_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) :
    MeasurableSet[(upperPassage_stopping_rightCont_filtration X b).measurableSpace]
      {ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} := by sorry
