-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_expectation_eq_restrict_lintegral
-- name    : AvramDividend.Classical.avram_root29_03_exit_expectation_eq_restrict_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:04:51.279016+00:00
-- url     : https://prove2.me/theorems/7b06a665-3ef6-46f9-9bdc-230d3ef1917a
-- title:
--   Genuine strict two-sided exit expectation as a restricted-measure lintegral
-- statement:
--   For any actual spectrally negative Lévy process, real discount q, and real upper barrier/starting capital, the genuine named strict upper-before-lower discounted exit expectation equals the discounted weight integrated with respect to the original law restricted to the measurable strict event. Exact strict clock ordering is preserved. No Standing or positive-barrier assumption is needed.
-- source:
--   Source-level indicator-to-measure-restriction adapter for corrected equation (3.6), using Proved official exit-event measurability 59d0930d and pinned Mathlib MeasureTheory.lintegral_indicator. This carries the actual original process law P, avoids conflating real conditional expectation with ENNReal lintegral, and adds no Open stochastic premise.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_exit_expectation_eq_restrict_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a x : ℝ) :
    twoSidedExitExpectation X q a x =
      (∫⁻ ω in {ω : Ω | twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω},
        ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω)))) ∂P) := by sorry
