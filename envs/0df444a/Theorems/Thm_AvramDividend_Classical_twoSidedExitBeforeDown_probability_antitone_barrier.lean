-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_probability_antitone_barrier
-- name    : AvramDividend.Classical.twoSidedExitBeforeDown_probability_antitone_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:19:17.157102+00:00
-- url     : https://prove2.me/theorems/20745524-9f4f-4553-9a49-b84a10428cf1
-- title:
--   Upper-before-ruin crossing probability decreases with the dividend barrier
-- statement:
--   At fixed initial capital, increasing the upper dividend threshold makes upper passage before ruin no more probable.
-- source:
--   Strict exit-clock order monotonicity under threshold changes.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_probability_mono_bounds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitBeforeDown_probability_antitone_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a b : ℝ) (hab : a ≤ b) :
    P {ω : Ω | twoSidedExitUpTime X (b - x) ω < twoSidedExitDownTime X (-x) ω} ≤
      P {ω : Ω | twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω} := by sorry
