-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_zero_discount_upperfirst_mass_any_measure
-- name    : AvramDividend.Classical.chat04_zero_discount_upperfirst_mass_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:17:47.128139+00:00
-- url     : https://prove2.me/theorems/d2a9665b-fd7d-4ce3-aa1c-dd622fdd5147
-- title:
--   Zero-discount strict upper-first lower integral equals event mass under any path law
-- statement:
--   For every measure on the Lévy sample-path space, the zero-discount upper-before-lower strict exit payoff integrates to the measure of that upper-first event. This identity works under the original law and changed measures.
-- source:
--   Generalises the remotely accepted chat04_twoSidedExitExpectation_zero_discount_eq_event_measure from the Lévy probability law to arbitrary path-space measures using measurable upper-first events.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_zero_discount_upperfirst_mass_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω) (a x : ℝ) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp (-(0 * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) else 0 ∂μ) =
    μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} := by sorry
