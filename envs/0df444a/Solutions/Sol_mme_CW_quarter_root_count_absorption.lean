-- Prove2me | solution 1 for mme_CW_quarter_root_count_absorption
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:14:56.923947+00:00
-- url     : https://prove2.me/submissions/2ddd955d-e0a4-4234-a796-0b5190166e01

import Mathlib.Analysis.SpecialFunctions.Exp

open Real

theorem solution
    (N A H k : ℕ) (raw loss W : ℝ)
    (hW : 0 ≤ W)
    (hprimary :
      (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
        (((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2)) * W)
    (hsecondary :
      ((H : ℝ) ^ 2) * Real.exp (-((N : ℝ) * loss)) ≤ (k : ℝ)) :
    (raw * Real.exp (-loss)) ^ (2 * N) ≤
      ((((A ^ 3) * k : ℕ) : ℝ)) * W := by
  have hid :
      (raw * Real.exp (-loss)) ^ (2 * N) =
        (raw * Real.exp (-(loss / 2))) ^ (2 * N) *
          Real.exp (-((N : ℝ) * loss)) := by
    have hexp :
        Real.exp (((2 * N : ℕ) : ℝ) * (-loss)) =
          Real.exp (((2 * N : ℕ) : ℝ) * (-(loss / 2))) *
            Real.exp (-((N : ℝ) * loss)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      hexp]
    ring
  rw [hid]
  calc
    (raw * Real.exp (-(loss / 2))) ^ (2 * N) *
          Real.exp (-((N : ℝ) * loss))
        ≤ ((((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2)) * W) *
            Real.exp (-((N : ℝ) * loss)) :=
      mul_le_mul_of_nonneg_right hprimary (Real.exp_pos _).le
    _ = (((A ^ 3 : ℕ) : ℝ) * W) *
          (((H : ℝ) ^ 2) * Real.exp (-((N : ℝ) * loss))) := by
      ring
    _ ≤ (((A ^ 3 : ℕ) : ℝ) * W) * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hsecondary
        (mul_nonneg (Nat.cast_nonneg _) hW)
    _ = ((((A ^ 3) * k : ℕ) : ℝ)) * W := by
      push_cast
      ring
