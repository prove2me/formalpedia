-- Prove2me | solution 1 for syracuse_relative_descent_iff_dyadic_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T12:10:22.29378+00:00
-- url     : https://prove2.me/submissions/679df513-715f-4e96-95fd-b476e1d81fb2

import Definitions.Def_syracuseStep

open Nat

theorem solution (y n b : ℕ)
    (hlo : 2^b*n ≤ 3*y+1) (hhi : 3*y+1 < 2^(b+1)*n) :
    syracuseStep y < n ↔ 2^(b+1) ∣ 3*y+1 := by
  let z := 3*y+1
  let e := z.factorization 2
  let o := ordCompl[2] z
  have eqn : 2^e*o = z := Nat.ordProj_mul_ordCompl_eq_self z 2
  have nz : z ≠ 0 := by dsimp [z]; omega
  change o < n ↔ 2^(b+1) ∣ z
  rw [Nat.prime_two.pow_dvd_iff_le_factorization nz]
  change o < n ↔ b+1 ≤ e
  constructor
  · intro ho
    by_contra! hb
    have hp : (2:ℕ)^e ≤ 2^b := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : 2^e*o < 2^b*n :=
      lt_of_le_of_lt (Nat.mul_le_mul_right o hp) (Nat.mul_lt_mul_of_pos_left ho (Nat.two_pow_pos b))
    change 2^b*n ≤ z at hlo
    omega
  · intro hb
    have hp : (2:ℕ)^(b+1) ≤ 2^e := Nat.pow_le_pow_right (by decide) hb
    apply Nat.lt_of_mul_lt_mul_left (show 2^e*o < 2^e*n from ?_)
    rw [eqn]
    exact lt_of_lt_of_le hhi (Nat.mul_le_mul_right n hp)
