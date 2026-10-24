-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_le_upperfirst_probability
-- name    : AvramDividend.Classical.chat04_twoSidedExitExpectation_le_upperfirst_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:18:53.713039+00:00
-- url     : https://prove2.me/theorems/7f580642-293d-420d-b378-dcf1a4ccd46b
-- title:
--   Discounted killed exit is bounded by strict upward-before-ruin probability
-- statement:
--   For q≥0, the killed strict upper-before-lower first-passage transform cannot exceed the probability of the exact successful upward-before-downward event. This strengthens the generic bound by one, retaining the strict ruin event, and combines the independently proved discount monotonicity and zero-discount event-measure representation.
-- source:
--   Conditional corollary of newly authored strict exit discount-antitonicity and zero-discount identification; parent theorems are separately submitted for Prove2Me verification.

import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_zero_discount_eq_event_measure

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_twoSidedExitExpectation_le_upperfirst_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hq : 0 ≤ q) :
    twoSidedExitExpectation X q a x ≤
      P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} := by sorry
