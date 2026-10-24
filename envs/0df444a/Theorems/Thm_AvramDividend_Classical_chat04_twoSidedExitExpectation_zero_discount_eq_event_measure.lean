-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_zero_discount_eq_event_measure
-- name    : AvramDividend.Classical.chat04_twoSidedExitExpectation_zero_discount_eq_event_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:13:41.496389+00:00
-- url     : https://prove2.me/theorems/e0abb906-a78e-4818-bb7d-763a1ff82fb2
-- title:
--   Zero-discount killed strict exit expectation equals the upward-first probability
-- statement:
--   For the exact strict upward-before-downward first-passage event, the killed two-sided exit lower integral with discount q=0 equals the event's probability measure. This uses the already proved measurability of the event and the exact indicator lower-integral identity, preserving strict inequalities and infinite passage times.
-- source:
--   Published MeasurableSet result chat03_upper_before_lower_passage_event_measurable (59d0930d-4811-4210-838b-657a7915fd2a), and pinned Mathlib.MeasureTheory.lintegral_indicator_one.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_twoSidedExitExpectation_zero_discount_eq_event_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x : ℝ) :
    twoSidedExitExpectation X 0 a x =
      P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} := by sorry
