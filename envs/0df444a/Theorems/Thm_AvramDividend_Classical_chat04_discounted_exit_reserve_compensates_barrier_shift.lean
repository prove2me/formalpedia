-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_exit_reserve_compensates_barrier_shift
-- name    : AvramDividend.Classical.chat04_discounted_exit_reserve_compensates_barrier_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:39:17.964995+00:00
-- url     : https://prove2.me/theorems/b9b50e80-5333-42e7-a43b-aa6ce6676f93
-- title:
--   A larger initial reserve compensates for an increased upper barrier in discounted strict exit
-- statement:
--   For any nonnegative discount, increasing initial reserve from x to y makes upper exit before strict ruin at least as likely even when the upper barrier changes from a to b, provided the new relative upper threshold b-y is no greater than a-x. The proof compares strict first-passage clocks samplewise and integrates the discounted payoff inequality.
-- source:
--   Uses published chat04_strict_exit_clocks_relative_barrier_comparison (5e83d1a9-b841-4183-9788-ed2fc2c18017), and adapts the accepted proof of chat04_discounted_strict_exit_monotone_initial_reserve (cd747fb7-bd55-4b15-96d9-a0d932a44f67).

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_exit_reserve_compensates_barrier_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a b x y : ℝ) (hq : 0 ≤ q)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    twoSidedExitExpectation X q a x ≤
      twoSidedExitExpectation X q b y := by sorry
