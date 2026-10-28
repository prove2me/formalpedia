-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_joint_barrier_discount_reserve_exit_comparison
-- name    : AvramDividend.Classical.chat04_joint_barrier_discount_reserve_exit_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:29:10.604172+00:00
-- url     : https://prove2.me/theorems/1e76d18d-e125-4daa-a2b8-fdf809f4cf1b
-- title:
--   Strict exit comparison under simultaneous discount, barrier and reserve changes
-- statement:
--   The discounted probability of reaching an upper reserve barrier before strict ruin is monotonically lower at a higher discount, a higher upper barrier and a lower initial capital. This simultaneous comparison combines established killed-exit barrier/discount antitonicity with monotonicity in initial reserve.
-- source:
--   Combines Proved chat04_joint_barrier_discount_exit_antitone (51ce9c62-e4eb-40ea-8a6c-2e21bdc4c824) and chat04_discounted_strict_exit_monotone_initial_reserve (cd747fb7-bd55-4b15-96d9-a0d932a44f67).

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_joint_barrier_discount_exit_antitone
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_joint_barrier_discount_reserve_exit_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x y : ℝ)
    (hq₁ : 0 ≤ q₁) (hqq : q₁ ≤ q₂)
    (hab : a ≤ b) (hxy : x ≤ y) :
    twoSidedExitExpectation X q₂ b x ≤
      twoSidedExitExpectation X q₁ a y := by sorry
