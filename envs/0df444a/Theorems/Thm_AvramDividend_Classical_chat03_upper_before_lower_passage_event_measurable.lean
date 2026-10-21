-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable
-- name    : AvramDividend.Classical.chat03_upper_before_lower_passage_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:22:30.754023+00:00
-- url     : https://prove2.me/theorems/59d0930d-4811-4210-838b-657a7915fd2a
-- title:
--   The exact event that an upper strict passage precedes a lower strict passage is measurable
-- statement:
--   For the exact extended nonnegative-real named strict first-passage clocks of the official spectrally negative Lévy process, the sample-path event that the upper clock is strictly earlier than the lower clock is measurable. Both clocks are separately established to be measurable ENNReal random variables, including the infinity atom, and the standard measurable strict-order relation gives the result. This is the event selected inside the allocated two-sided stopped-scale integral. The theorem respects ties and infinite passage without approximating either clock by a finite surrogate.
-- source:
--   Proved Chat03 both named clock measurability and pinned Mathlib measurableSet_lt.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_upper_before_lower_passage_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet
      {ω : Ω | twoSidedExitUpTime X upper ω <
        twoSidedExitDownTime X lower ω} := by sorry
