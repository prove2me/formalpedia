-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_zero_discount_eq_event_measure_any_measure
-- name    : AvramDividend.Classical.chat04_strict_exit_zero_discount_eq_event_measure_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:59:38.701125+00:00
-- url     : https://prove2.me/theorems/4bd42c8b-4c34-4352-85db-af67a69479e2
-- title:
--   Strict upward-before-ruin zero-discount event mass under any measure
-- statement:
--   For any trajectory-space measure μ, the strict upper-first lower integral at zero discount coincides exactly with μ of the measurable event that upper passage precedes ruin. This lets tilted finite or sigma-finite laws use the same event-mass bridge as the physical process measure.
-- source:
--   Adapts the canonically Proved zero-discount identity AvramDividend.Classical.chat04_twoSidedExitExpectation_zero_discount_eq_event_measure, UUID e0abb906-a78e-4818-bb7d-763a1ff82fb2, and the Proved measurable strict-event theorem, without a probability-measure assumption.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_zero_discount_eq_event_measure_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω) (a x : ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(0 * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) =
    μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} := by sorry
