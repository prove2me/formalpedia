-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_before_upper_passage_event_measurable
-- name    : AvramDividend.Classical.chat04_lower_before_upper_passage_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T12:05:55.370912+00:00
-- url     : https://prove2.me/theorems/9b56797c-0f5e-4534-aa9d-7590671aac82
-- title:
--   Strict lower-first ruin-before-upper-exit passage event is measurable
-- statement:
--   For the exact strict Lévy first-passage clocks, the event of lower exit occurring strictly before upper exit is Borel measurable in the sample-path space, even when either clock may be infinite.
-- source:
--   Reverse the measurable-order arguments in the proved joint passage-clock measurability theorem.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_lower_before_upper_passage_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet
      {ω : Ω | twoSidedExitDownTime X lower ω <
        twoSidedExitUpTime X upper ω} := by sorry
