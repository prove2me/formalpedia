-- Prove2me | solution 1 for syracuse_fixed_point_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:14:50.380668+00:00
-- url     : https://prove2.me/submissions/5ed79bfd-6071-4b4d-ada4-0a06a292e1b8

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem solution (m : ℕ) (hm : 0 < m) (hfix : syracuseStep m = m) : m = 1 := by
  set v := (3 * m + 1).factorization 2 with hv
  -- the 2-part times the odd part recovers 3 * m + 1, and the odd part is m itself
  have hsplit : 2 ^ v * m = 3 * m + 1 := by
    have := Nat.ordProj_mul_ordCompl_eq_self (3 * m + 1) 2
    rwa [show ordCompl[2] (3 * m + 1) = m from hfix] at this
  -- so m * (2 ^ v - 3) = 1, which pins both m and v
  rcases Nat.lt_or_ge v 3 with hlt | hge
  · interval_cases v <;> omega
  · have h8 : 8 ≤ 2 ^ v := by
      calc (8:ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hge
    have : 8 * m ≤ 2 ^ v * m := Nat.mul_le_mul_right m h8
    omega
