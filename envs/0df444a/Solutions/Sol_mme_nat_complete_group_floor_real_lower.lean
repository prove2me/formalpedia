-- Prove2me | solution 1 for mme_nat_complete_group_floor_real_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:36:18.338783+00:00
-- url     : https://prove2.me/submissions/874fb9f1-6e4e-4855-a15f-6c9fc52f1164

import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (n g : ℕ) (A : ℝ)
    (hg : 0 < g)
    (hlarge : 2 * (g : ℝ) ≤ A)
    (hlower : A ≤ (n : ℝ)) :
    A / (2 * (g : ℝ)) ≤ ((n / g : ℕ) : ℝ) := by
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hnUpperNat : n < g * (n / g + 1) :=
    Nat.lt_mul_div_succ n hg
  have hnUpper : (n : ℝ) < (g : ℝ) * (((n / g : ℕ) : ℝ) + 1) := by
    exact_mod_cast hnUpperNat
  have hhalf : A / 2 < (g : ℝ) * ((n / g : ℕ) : ℝ) := by
    nlinarith
  apply (div_le_iff₀ (mul_pos (by norm_num) hgR)).2
  nlinarith
