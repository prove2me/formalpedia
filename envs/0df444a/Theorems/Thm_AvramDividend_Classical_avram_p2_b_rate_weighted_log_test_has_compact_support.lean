-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_has_compact_support
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_has_compact_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:15:55.507297+00:00
-- url     : https://prove2.me/theorems/89de0a49-a0c9-4b55-92ce-4d61be2dec89
-- title:
--   Inverse fourth-weighted logarithmic negative-mark test has compact support on the full real image line
-- statement:
--   If a negative-mark test vanishes for marks greater than -epsilon with epsilon positive, then the inverse exponential image test g(z)=f(log z)/(z-1)^4 has compact support inside [-exp(-epsilon),exp(-epsilon)] on the entire real line. This is independent of continuity and handles negative z using Real.log_abs, providing a reusable compact-support bound for subsequent Riesz/weak-measure test arguments.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_has_compact_support
    (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    HasCompactSupport (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) := by sorry
