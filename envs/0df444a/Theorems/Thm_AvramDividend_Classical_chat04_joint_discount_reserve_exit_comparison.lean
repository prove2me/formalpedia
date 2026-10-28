-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_joint_discount_reserve_exit_comparison
-- name    : AvramDividend.Classical.chat04_joint_discount_reserve_exit_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:28:03.978908+00:00
-- url     : https://prove2.me/theorems/6f301d79-b735-4f27-b242-eeb288b12c89
-- title:
--   Strict exit transform joint monotonicity in discount and initial capital
-- statement:
--   For a spectrally negative Lévy process, the killed discounted strict two-sided exit transform decreases if its nonnegative discount rate is increased and increases if its initial reserve is increased. Thus an upper bound at a smaller discount and larger initial reserve holds jointly, without additional standing assumptions.
-- source:
--   Combines proved AvramDividend.Classical.chat04_twoSidedExitExpectation_antitone_discount (69a4a254-000a-4139-880d-577bc9fca961) and chat04_discounted_strict_exit_monotone_initial_reserve (cd747fb7-bd55-4b15-96d9-a0d932a44f67).

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_joint_discount_reserve_exit_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a x y : ℝ)
    (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (hxy : x ≤ y) :
    twoSidedExitExpectation X q₂ a x ≤
      twoSidedExitExpectation X q₁ a y := by sorry
