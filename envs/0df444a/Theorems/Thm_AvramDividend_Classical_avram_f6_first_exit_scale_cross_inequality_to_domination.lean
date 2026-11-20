-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_first_exit_scale_cross_inequality_to_domination
-- name    : AvramDividend.Classical.avram_f6_first_exit_scale_cross_inequality_to_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:04:14.954433+00:00
-- url     : https://prove2.me/theorems/ea3f6553-53c7-4014-8836-966312fd0ef1
-- title:
--   Original first-exit w(y)W(1) inequality gives scale-function domination w≤A W
-- statement:
--   Under actual q-scale W(1)>0, HJB w(1)≥0 and genuine killed first-exit cross inequality w(y)W(1)≤w(1)W(y) for y≥1, obtain nonnegative A=w(1)/W(1) with w(y)≤A W(y). A direct algebraic source interface to original topcap HJB exponential growth.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_f6_first_exit_scale_cross_inequality_to_domination
    (w W : ℝ → ℝ)
    (hw1 : 0 ≤ w 1) (hW1 : 0 < W 1)
    (hExit : ∀ y : ℝ, 1 ≤ y →
      w y * W 1 ≤ w 1 * W y) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y := by sorry
