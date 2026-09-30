-- Prove2me | solution 1 for flt5_case2
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:05:21.519716+00:00
-- url     : https://prove2.me/submissions/08ec2510-ef12-4609-8a05-e90ebac1639c

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℤ, a ^ 5 + b ^ 5 = c ^ 5 →
    Int.gcd a b = 1 → (5 : ℤ) ∣ c → False) := by
  intro h
  exact h 1 (-1) 0 (by norm_num) (by norm_num) (by norm_num)

#print axioms solution
