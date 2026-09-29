-- Prove2me | solution 1 for gcd_coprime_mul
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:14:41.639908+00:00
-- url     : https://prove2.me/submissions/fb05c774-e744-4f0f-8d9a-c804ef0fb265

-- gcd_coprime_mul proof
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem solution (a b c : ℤ) (h1 : Int.gcd a b = 1) (h2 : Int.gcd a c = 1) : Int.gcd a (b * c) = 1 := by
  have hcop1 : Nat.Coprime a.natAbs b.natAbs := h1
  have hcop2 : Nat.Coprime a.natAbs c.natAbs := h2
  have hcop_mul : Nat.Coprime a.natAbs (b * c).natAbs := by
    rw [Int.natAbs_mul]
    exact hcop1.mul_right hcop2
  exact hcop_mul
