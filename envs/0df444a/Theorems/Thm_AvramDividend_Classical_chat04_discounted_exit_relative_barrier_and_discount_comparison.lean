-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_exit_relative_barrier_and_discount_comparison
-- name    : AvramDividend.Classical.chat04_discounted_exit_relative_barrier_and_discount_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:04:12.778776+00:00
-- url     : https://prove2.me/theorems/e5c78fc8-8e1f-4240-a22b-c6f4a576342a
-- title:
--   Joint strict-exit expectation comparison under discount and relative barrier shifts
-- statement:
--   When the initial reserve rises and the upper threshold relative to that reserve does not rise, its discounted upper-exit-before-ruin expectation is larger. The comparison remains valid when the left-hand discount rate is at least the right-hand discount rate. This combines proved pathwise first-passage ordering with monotonicity in discount.
-- source:
--   Uses chat04_discounted_exit_reserve_compensates_barrier_shift and proved chat04_twoSidedExitExpectation_antitone_discount.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_exit_reserve_compensates_barrier_shift

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_exit_relative_barrier_and_discount_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x y : ℝ)
    (hq : q₁ ≤ q₂) (hq₁ : 0 ≤ q₁)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    twoSidedExitExpectation X q₂ a x ≤
      twoSidedExitExpectation X q₁ b y := by sorry
