-- Prove2me | solution 1 for gcd_coprime_sub
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:14:41.385058+00:00
-- url     : https://prove2.me/submissions/d0e20262-f04f-455c-a2cb-3d288ed849fe

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) (h : Int.gcd a b = 1) : Int.gcd (a - b) b = 1 := by
  rw [Int.gcd_comm]
  -- goal: b.gcd (a - b) = 1
  rw [show a - b = a + (-1) * b from by ring]
  have h2 := @Int.gcd_add_mul_right_right b a (-1)
  -- h2 : b.gcd (a + (-1) * b) = b.gcd a
  rw [h2, Int.gcd_comm]
  exact h
