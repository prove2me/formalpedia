-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_inclusive_cash_and_continuous_terminal_rightclock_limit
-- name    : AvramDividend.Classical.avram_f6_original_inclusive_cash_and_continuous_terminal_rightclock_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:17:30.177543+00:00
-- url     : https://prove2.me/theorems/5b537c13-6ac4-4c66-8d2f-d7ef50e3e22b
-- title:
--   Original right-clock continuous terminal plus inclusive toReal cash converges retaining contact atom
-- statement:
--   For antitone actual physical-clock endpoints approaching the subordinate stopped time, a terminal reward right-continuous within the right-side physical clock plus finite inclusive Iic paid cash converges to the exact value including the payment atom at the stopped clock. This is deterministic clock/contact arithmetic required by original F6 Fatou and avoids any assumed HJB upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_closed_cash_antitone_clock_limit
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_inclusive_cash_and_continuous_terminal_rightclock_limit
    (μ : Measure ℝ) (a : ℕ → ℝ) (s : ℝ)
    (ha : Antitone a) (hl : Tendsto a atTop (𝓝 s))
    (hfinite : ∃ n, μ (Iic (a n)) ≠ ∞)
    (f : ℝ → ℝ)
    (hf : ContinuousWithinAt f (Ici s) s) :
    Tendsto (fun n => f (a n) + (μ (Iic (a n))).toReal)
      atTop (𝓝 (f s + (μ (Iic s)).toReal)) := by sorry
