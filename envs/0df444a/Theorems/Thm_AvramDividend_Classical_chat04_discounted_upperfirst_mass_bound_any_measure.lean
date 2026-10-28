-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_mass_bound_any_measure
-- name    : AvramDividend.Classical.chat04_discounted_upperfirst_mass_bound_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:10:54.380848+00:00
-- url     : https://prove2.me/theorems/1ceb1831-b9e6-472c-8a23-0fdb57db9081
-- title:
--   Discounted strict upper-first mass bound under an arbitrary path-space measure
-- statement:
--   For any nonnegative discount rate and any measure on the Lévy sample-path space, the killed discounted upper-exit-before-ruin reward has lower integral at most the measure of the upper-first event. This is a measure-independent version of the usual discounted exit probability bound, useful under Esscher tilts.
-- source:
--   Adapts remotely accepted chat04_twoSidedExitExpectation_le_one (dde72b60-9dac-4c91-91bb-f67d00e44444) and chat04_twoSidedExitExpectation_zero_discount_eq_event_measure (e0abb906-a78e-4818-bb7d-763a1ff82fb2), using chat03_upper_before_lower_passage_event_measurable.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_upperfirst_mass_bound_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
    μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} := by sorry
