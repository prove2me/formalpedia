-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_zero_discount_lowerfirst_mass_any_measure
-- name    : AvramDividend.Classical.chat04_zero_discount_lowerfirst_mass_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T12:11:57.728954+00:00
-- url     : https://prove2.me/theorems/14b8a199-036c-439e-a4c2-b31ddecb399f
-- title:
--   Zero-discount strict ruin-before-upper-exit expectation equals ruin-first event mass for any path measure
-- statement:
--   For any path-space measure, the discounted lower-first exit weight at zero discount integrates to exactly the measure of the event that ruin strictly precedes upper exit.
-- source:
--   Measurability of the strict lower-first passage event and the standard lower integral of a set indicator.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_before_upper_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_zero_discount_lowerfirst_mass_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω) (a x : ℝ) :
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω then
          ENNReal.ofReal (Real.exp (-(0 * ENNReal.toReal
            (twoSidedExitDownTime X (-x) ω)))) else 0 ∂μ) =
    μ {ω : Ω | twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω} := by sorry
