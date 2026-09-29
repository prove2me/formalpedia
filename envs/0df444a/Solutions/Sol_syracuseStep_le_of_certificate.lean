-- Prove2me | solution 1 for syracuseStep_le_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:48:23.940327+00:00
-- url     : https://prove2.me/submissions/9ba2ae4f-7e9d-4a62-8d44-61e3551117b3

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem solution (a : ℕ) {x y : ℕ} (h : 3 * x + 1 = 2 ^ a * y) :
    syracuseStep x ≤ y := by
  have hne : 3 * x + 1 ≠ 0 := by omega
  have hle : a ≤ (3 * x + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 ⟨y, h⟩
  show ordCompl[2] (3 * x + 1) ≤ y
  calc
    (3 * x + 1) / 2 ^ ((3 * x + 1).factorization 2)
        ≤ (3 * x + 1) / 2 ^ a :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hle) (by positivity)
    _ = y := by rw [h, Nat.mul_div_cancel_left _ (by positivity)]
