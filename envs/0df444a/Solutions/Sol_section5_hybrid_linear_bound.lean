-- Prove2me | solution 1 for section5_hybrid_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:24.187583+00:00
-- url     : https://prove2.me/submissions/1734b651-72db-42f4-b16d-a40639cbedff

import Mathlib
set_option autoImplicit false
open MeasureTheory
theorem solution (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : (n:ℝ)*δ ≤ 1/2) : (1+δ)^n-1 ≤ 2*n*δ := by
  have hp : (1+δ)^n ≤ Real.exp ((n:ℝ)*δ) := by
    calc
      _ ≤ (Real.exp δ)^n := pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp δ) n
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hnδ : 0 ≤ (n:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ
  have he := Real.abs_exp_sub_one_le (x := (n:ℝ)*δ)
    (by rw [abs_of_nonneg hnδ]; linarith)
  have hh := (le_abs_self (Real.exp ((n:ℝ)*δ)-1)).trans he
  rw [abs_of_nonneg hnδ] at hh
  nlinarith
