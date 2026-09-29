-- Prove2me | solution 1 for syracuseStep_eq_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:48:23.463783+00:00
-- url     : https://prove2.me/submissions/5cea136b-fc1a-40f9-9f7e-625e3d2dcf9b

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem solution (a : ℕ) {x y : ℕ} (h : 3 * x + 1 = 2 ^ a * y) (hy : Odd y) :
    syracuseStep x = y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp [Nat.odd_iff] at hy
  have hfac : (3 * x + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hy0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * x + 1) = y
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]
