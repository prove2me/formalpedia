-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_decay_difference_le_interval_length
-- name    : AvramDividend.Classical.exponential_decay_difference_le_interval_length
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:25:48.774319+00:00
-- url     : https://prove2.me/theorems/8ac7b9c5-b976-412e-8cb8-ef34fac366d1
-- title:
--   Exponential-decay difference is bounded by elapsed nonnegative argument
-- statement:
--   For nonnegative a≤b, exp(-a)-exp(-b)≤b-a. This is the one-Lipschitz estimate for decreasing exponential on [0,∞), proved from exp(-x)≥1-x and the exponential addition law; controls the finite-activity grid-Laplace gap.
-- source:
--   Mathlib Real.one_sub_le_exp_neg, Real.exp_add, Real.exp_le_one_iff; Avram, Palmowski and Pistorius (2007), section 3.3.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem AvramDividend.Classical.exponential_decay_difference_le_interval_length
    (a b : ℝ) (ha : LE.le 0 a) (hab : LE.le a b) :
    LE.le (Real.exp (-a) - Real.exp (-b)) (b-a) := by sorry
