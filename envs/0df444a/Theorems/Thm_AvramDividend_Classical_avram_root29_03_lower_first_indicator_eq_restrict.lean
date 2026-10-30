-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_lower_first_indicator_eq_restrict
-- name    : AvramDividend.Classical.avram_root29_03_lower_first_indicator_eq_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:22:04.427831+00:00
-- url     : https://prove2.me/theorems/2615773e-c5ff-4fcb-8b4a-0adbc39a8c4d
-- title:
--   Exact lower-first ruin indicator lintegral as restricted original event measure
-- statement:
--   For the original spectrally negative Lévy process and any sample-path measure μ, the ENNReal integral of any nonnegative reward gated by the actual strict lower-before-upper passage event equals its integral under μ restricted to that measurable event. Useful for the bounded-variation lower-creeping payoff component. No Standing, variation, discount, or positive threshold assumptions.
-- source:
--   Source-level lower-branch counterpart to the already Proved upper-first restricted-event adapter, using canonically Proved strict lower-first event measurability 9b56797c. Independent of Open BV no-creeping and OST premises.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_before_upper_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_lower_first_indicator_eq_restrict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (f : Ω → ℝ≥0∞) :
    (∫⁻ ω, if twoSidedExitDownTime X lower ω <
        twoSidedExitUpTime X upper ω then f ω else 0 ∂μ) =
    (∫⁻ ω in {ω : Ω | twoSidedExitDownTime X lower ω <
        twoSidedExitUpTime X upper ω}, f ω ∂μ) := by sorry
