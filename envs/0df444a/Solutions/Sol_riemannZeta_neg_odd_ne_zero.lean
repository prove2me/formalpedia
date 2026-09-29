-- Prove2me | solution 1 for riemannZeta_neg_odd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:27:59.613572+00:00
-- url     : https://prove2.me/submissions/1977ea32-a07d-42a8-b179-7e53b9bc6d1f

import Mathlib

open Complex

theorem solution (n : ℕ) (hn : Odd n) : riemannZeta (-(n : ℂ)) ≠ 0 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : k + 1 ≠ 0 := by omega
  have hzpos : riemannZeta ((2 * (k + 1) : ℕ) : ℂ) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    change 1 ≤ ((2 * (k + 1) : ℕ) : ℝ)
    exact_mod_cast (show 1 ≤ 2 * (k + 1) by omega)
  have hb : (bernoulli (2 * (k + 1)) : ℂ) ≠ 0 := by
    intro hb
    apply hzpos
    have hcast : (((2 * (k + 1) : ℕ) : ℂ)) = 2 * (k + 1) := by norm_num
    rw [hcast]
    have hf := riemannZeta_two_mul_nat (k := k + 1) hk
    norm_num [Nat.cast_add] at hf
    rw [hf]
    simp [hb]
  rw [riemannZeta_neg_nat_eq_bernoulli]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · convert hb using 1 <;> ring
  · intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    have hk0 : (0 : ℝ) ≤ k := by positivity
    linarith
