-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:43:50.92954+00:00
-- url     : https://prove2.me/theorems/7708f0f6-b40e-4ff8-93a3-d0ce79d00e1d
-- title:
--   Nonnegative-time original discount is Lipschitz with constant q
-- statement:
--   For discount rate q≥0 and 0≤a≤b, the difference between the exact exponential discount factors at a and b is at most q(b-a). This global one-sided Lipschitz bound quantitatively controls the within-cell discount oscillation on any finite dividend-payment mesh without assuming q is strictly positive.
-- source:
--   Real.one_sub_le_exp_neg and Real.exp_add in Mathlib.Analysis.Complex.Exponential; Avram controlled Proposition 4(i) time-discount term

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz (q a b : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-(q * a)) ≤ Real.exp (-(q * b)) + q * (b - a) := by sorry
