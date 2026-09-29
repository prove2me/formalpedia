-- Prove2me | solution 1 for gcd_coprime_add
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:10:09.268271+00:00
-- url     : https://prove2.me/submissions/071f2a58-2724-429a-9b45-bbeb0db6c4a4

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem solution (a b : ℤ) (h : Int.gcd a b = 1) : Int.gcd (a + b) b = 1 := by
  rw [Int.gcd_comm]
  have hab := @Int.gcd_add_mul_right_right b a 1
  simp only [one_mul] at hab
  -- hab : b.gcd (a + b) = b.gcd a
  rw [hab, Int.gcd_comm]
  exact h
