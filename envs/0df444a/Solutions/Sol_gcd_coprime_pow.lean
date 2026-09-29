-- Prove2me | solution 1 for gcd_coprime_pow
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:12:40.080272+00:00
-- url     : https://prove2.me/submissions/c7090371-3cd4-469f-a149-c3cb8562cbba

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem solution (a b : ℤ) (n : ℕ) (h : Int.gcd a b = 1) : Int.gcd a (b ^ n) = 1 := by
  have hcop : Nat.Coprime a.natAbs b.natAbs := h
  have hcop_pow : Nat.Coprime a.natAbs (b ^ n).natAbs := by
    rw [Int.natAbs_pow]
    exact hcop.pow_right n
  exact hcop_pow
