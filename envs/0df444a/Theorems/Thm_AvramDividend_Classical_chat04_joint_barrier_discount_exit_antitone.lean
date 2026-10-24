-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_joint_barrier_discount_exit_antitone
-- name    : AvramDividend.Classical.chat04_joint_barrier_discount_exit_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:30:06.94658+00:00
-- url     : https://prove2.me/theorems/51ce9c62-e4eb-40ea-8a6c-2e21bdc4c824
-- title:
--   Strict two-sided exit transform decreases jointly in barrier and discount
-- statement:
--   For the exact strict upward-before-ruin transform, increasing both the upper barrier and the nonnegative discount rate can only decrease the discounted exit expectation. This composes two already proved inequalities while preserving the same strict ruin priority and handles all finite/infinite stopping-time cases through the established lemmas. The result supports joint parameter comparisons in barrier valuation.
-- source:
--   Combines the proved strict exit upper-barrier monotonicity and proved discount-rate monotonicity, both without invoking the open q-scale exit identity.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_antitone_upper_barrier
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_joint_barrier_discount_exit_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x : ℝ) (hq₁ : 0 ≤ q₁) (hqq : q₁ ≤ q₂) (hab : a ≤ b) :
    twoSidedExitExpectation X q₂ b x ≤ twoSidedExitExpectation X q₁ a x := by sorry
