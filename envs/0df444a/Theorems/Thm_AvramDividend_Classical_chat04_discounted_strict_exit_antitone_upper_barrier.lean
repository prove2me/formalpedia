-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_antitone_upper_barrier
-- name    : AvramDividend.Classical.chat04_discounted_strict_exit_antitone_upper_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:35:02.084358+00:00
-- url     : https://prove2.me/theorems/96cf53a1-b4da-4ce3-9040-34130de9d6a4
-- title:
--   Discounted strict exit expectation decreases with the upper barrier
-- statement:
--   At nonnegative discount, raising the upward barrier weakens the strict upward-before-ruin payoff. On paths that successfully reach the higher level, the lower-level upcrossing happens no later, so exponential discount is larger at the lower level; other paths contribute zero on the higher-barrier side. Monotonicity of the nonnegative lower integral gives the precise result. Infinity is handled by the successful-exit event.
-- source:
--   Pathwise strict-barrier comparison and exponential monotonicity; Avram et al. 2007 equation (3.6).

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_success_antitone_upper_barrier

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_strict_exit_antitone_upper_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a b x : ℝ)
    (hq : 0 ≤ q) (hab : a ≤ b) :
    twoSidedExitExpectation X q b x ≤ twoSidedExitExpectation X q a x := by sorry
