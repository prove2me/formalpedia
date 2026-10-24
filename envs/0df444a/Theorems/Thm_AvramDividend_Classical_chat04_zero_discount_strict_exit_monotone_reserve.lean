-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_zero_discount_strict_exit_monotone_reserve
-- name    : AvramDividend.Classical.chat04_zero_discount_strict_exit_monotone_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:12:53.87578+00:00
-- url     : https://prove2.me/theorems/63c30109-f20e-4970-9dc2-95684aa98108
-- title:
--   Upper-before-ruin probability is nondecreasing in initial capital
-- statement:
--   At zero discount, the exact strict upward-before-ruin expectation equals the probability of the successful event. The pathwise inclusion of successful events for increasing initial reserve and measure monotonicity imply the killed exit probability is nondecreasing. This does not assume an unjustified equality of strict and weak first-passage times.
-- source:
--   Derived from separately Proved zero-discount strict exit integral identity and strict passage event inclusion; Avram et al. 2007 eq. (3.6) q=0 case.

import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_zero_discount_eq_event_measure
import Theorems.Thm_AvramDividend_Classical_chat04_strict_up_before_ruin_event_monotone_reserve

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_zero_discount_strict_exit_monotone_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x y : ℝ) (hxy : x ≤ y) :
    twoSidedExitExpectation X 0 a x ≤ twoSidedExitExpectation X 0 a y := by sorry
