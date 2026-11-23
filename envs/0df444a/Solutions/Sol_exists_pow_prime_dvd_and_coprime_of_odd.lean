-- Prove2me | solution 1 for exists_pow_prime_dvd_and_coprime_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:56.515797+00:00
-- url     : https://prove2.me/submissions/e98226a7-f07d-4278-877f-d389608af8e3

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
import Definitions.Def_MillerRabin_Lemmas
import Theorems.Thm_exists_pow_prime_dvd_and_coprime

set_option autoImplicit false
open Nat
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) (ho : Odd n) (hnp : ¬IsPrimePow n) :
    ∃ p s k : ℕ, p.Prime ∧ 0 < s ∧ n = p ^ s * k ∧ (p ^ s).Coprime k ∧ 2 < k ∧ 2 < p ^ s := by
  have ⟨p, s, k, pp, spos, hk, hcoprime⟩ := exists_pow_prime_dvd_and_coprime hn
  use p, s, k, pp, spos, hk, hcoprime
  constructor
  · by_contra
    interval_cases k
    · simp [hk] at hn
    · exact hnp ⟨p, s, pp.prime, spos, by simpa using hk.symm⟩
    · exact ho.not_two_dvd_nat ⟨p ^ s, Nat.mul_comm _ _ ▸ hk⟩
  · apply lt_of_le_of_ne
    · exact (s.le_self_pow spos.ne' 2).trans (Nat.pow_le_pow_left pp.two_le s)
    · exact fun h ↦ ho.not_two_dvd_nat ⟨k, h ▸ hk⟩
