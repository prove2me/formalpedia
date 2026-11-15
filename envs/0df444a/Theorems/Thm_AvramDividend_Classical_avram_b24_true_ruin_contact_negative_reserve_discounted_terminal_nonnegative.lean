-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_true_ruin_contact_negative_reserve_discounted_terminal_nonnegative
-- name    : AvramDividend.Classical.avram_b24_true_ruin_contact_negative_reserve_discounted_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:00:52.0482+00:00
-- url     : https://prove2.me/theorems/53679de9-d626-4e0c-82e2-0e30e907af85
-- title:
--   Negative or zero ruin-contact terminal reserve has nonnegative discounted reward
-- statement:
--   If a payoff vanishes strictly below zero and is nonnegative at zero, its discounted reward at any nonpositive reserve is nonnegative. This separately accounts for ruin with downward overshoot and exact zero contact.
-- source:
--   Exact terminal contact sign needed for original ruin-clipped Ito cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_b24_true_ruin_contact_negative_reserve_discounted_terminal_nonnegative
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) (t : ℝ≥0) (y : ℝ) (hy : y ≤ 0) :
    0 ≤ Real.exp (-(q * (t : ℝ))) * w y := by sorry
