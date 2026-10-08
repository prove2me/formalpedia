-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_tsum_of_quadratic_exp_bound
-- name    : AvramDividend.Classical.continuousOn_tsum_of_quadratic_exp_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T11:43:18.477609+00:00
-- url     : https://prove2.me/theorems/05474add-f20e-40a7-a056-1bc25e5d988a
-- title:
--   A quadratic-exponential majorant gives continuity of a function series on a set
-- statement:
--   Let f_n be real-valued functions continuous on a set K. If on K each |f_n(x)| is bounded by C n^2 exp(-r n) for a fixed r>0, then the pointwise infinite sum Σ f_n(x) is continuous on K. The proof is the Weierstrass M-test using the pinned Mathlib summability of n^k exp(-r n) and continuousOn_tsum. This is the exact deterministic uniform-convergence step needed for the bounded-variation absolutely-continuous scale-function renewal density series.
-- source:
--   Pinned Mathlib Real.summable_pow_mul_exp_neg_nat_mul and continuousOn_tsum; deterministic Weierstrass M-test. Used by the BV+AC renewal-density route in Chan–Kyprianou–Savov smoothness theory.

import Mathlib
open Set

theorem AvramDividend.Classical.continuousOn_tsum_of_quadratic_exp_bound
    (f : ℕ → ℝ → ℝ) (K : Set ℝ) (C r : ℝ) (hr : 0 < r)
    (hf : ∀ n : ℕ, ContinuousOn (f n) K)
    (hbound : ∀ n : ℕ, ∀ x ∈ K,
      ‖f n x‖ ≤ C * ((n : ℝ) ^ 2 * Real.exp (-r * (n : ℝ)))) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, f n x) K := by sorry
