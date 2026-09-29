-- Prove2me | solution 1 for waiting_time_cdf_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T22:12:16.851507+00:00
-- url     : https://prove2.me/submissions/2fccfaa3-793e-4c0e-93ab-d0217ccfae73

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
open scoped BigOperators
open Finset

theorem solution (N mp : ℕ) (lam : ℝ) (h : mp < N) :
    (∑ k ∈ Finset.Ico (mp+1) (N+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * (0:ℝ)))) ^ k
        * (Real.exp (-(lam * (0:ℝ)))) ^ (N - k)) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  have h0 : Real.exp (-(lam * (0:ℝ))) = 1 := by
    rw [mul_zero, neg_zero, Real.exp_zero]
  rw [h0]
  rw [show (1:ℝ) - 1 = 0 by ring]
  rw [zero_pow (by omega : k ≠ 0)]
  ring
