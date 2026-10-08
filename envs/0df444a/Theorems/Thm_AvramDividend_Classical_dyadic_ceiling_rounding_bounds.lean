-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds
-- name    : AvramDividend.Classical.dyadic_ceiling_rounding_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:39:59.807752+00:00
-- url     : https://prove2.me/theorems/57b560d3-993c-406e-b3e8-bd006ac45674
-- title:
--   Dyadic upward rounding stays within one mesh step
-- statement:
--   For a nonnegative time t and dyadic resolution n, rounding 2^n t upward to the nearest integer and dividing by 2^n gives a time not earlier than t and strictly less than t+2^{-n}. The proof is a direct application of Nat.le_ceil and Nat.ceil_lt_add_one followed by division by the positive mesh multiplier. This reusable exact rounding estimate supplies the domination and convergence of finite-grid upper approximations of bounded stopping times needed for the bounded-stopping Lévy increment Laplace law.
-- source:
--   Mathlib Nat.le_ceil and Nat.ceil_lt_add_one, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474; dyadic stopping-time proof of the strong Markov property.

import Mathlib
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dyadic_ceiling_rounding_bounds
    (t : ℝ≥0) (n : ℕ) :
    (t : ℝ) ≤
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n ∧
      (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n <
        (t : ℝ) + 1 / (2 : ℝ) ^ n := by sorry
