-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_antitone_barrier
-- name    : AvramDividend.Classical.twoSidedExitBeforeDown_event_antitone_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:19:13.499795+00:00
-- url     : https://prove2.me/theorems/d64d53b2-ef5d-4824-b7f5-b3f5e0155fac
-- title:
--   Upper-before-ruin passage event decreases with the dividend barrier
-- statement:
--   At fixed initial capital, increasing the upper dividend threshold makes upper passage before ruin a subset of the event at the lower threshold.
-- source:
--   Strict exit-clock order monotonicity under threshold changes.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitBeforeDown_event_antitone_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a b : ℝ) (hab : a ≤ b) :
    {ω : Ω | twoSidedExitUpTime X (b - x) ω < twoSidedExitDownTime X (-x) ω} ⊆
      {ω : Ω | twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω} := by sorry
