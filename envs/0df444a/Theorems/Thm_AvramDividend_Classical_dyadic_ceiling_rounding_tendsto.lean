-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_tendsto
-- name    : AvramDividend.Classical.dyadic_ceiling_rounding_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:44:14.733255+00:00
-- url     : https://prove2.me/theorems/eb5240c4-480a-4f01-a31c-d944c87b2b7b
-- title:
--   Dyadic upper rounding of a nonnegative time converges to that time
-- statement:
--   The upward dyadic rounding of each fixed nonnegative time t converges back to t as the dyadic grid is refined. The complete inequality t≤ceil(2^n t)/2^n<t+2^{-n}, provided by the independently published dyadic ceiling bounds, sandwiches the rounded values between a constant sequence and an upper sequence converging to t because (1/2)^n→0. This pointwise result is a direct building block for constructing bounded stopping-time approximations and proving right-continuous convergence of the post-stopping Lévy increments.
-- source:
--   Pinned Mathlib Nat.ceil bounds, tendsto_pow_atTop_nhds_zero_of_lt_one and tendsto_of_tendsto_of_tendsto_of_le_of_le; Lévy strong-Markov dyadic approximation.

import Mathlib
open Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dyadic_ceiling_rounding_tendsto
    (t : ℝ≥0) :
    Tendsto
      (fun n : ℕ =>
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n)
      atTop (𝓝 (t : ℝ)) := by sorry
