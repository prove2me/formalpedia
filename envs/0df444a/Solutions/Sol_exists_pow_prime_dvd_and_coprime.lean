-- Prove2me | solution 1 for exists_pow_prime_dvd_and_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:19.347447+00:00
-- url     : https://prove2.me/submissions/000c6c62-ad36-40e1-aaaa-081fc48303fa

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
import Definitions.Def_MillerRabin_Lemmas

set_option autoImplicit false
open Nat
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) :
    ∃ p s k : ℕ, p.Prime ∧ 0 < s ∧ n = p ^ s * k ∧ (p ^ s).Coprime k := by
  let ⟨p, pp, hp⟩ := exists_prime_and_dvd (lt_of_succ_le hn).ne'
  have : Fact p.Prime := ⟨pp⟩
  let s := padicValNat p n
  obtain ⟨k, hk : n = p ^ s * k⟩ := pow_padicValNat_dvd
  use p, s, k, pp, one_le_padicValNat_of_dvd (two_pos.trans_le hn).ne' hp, hk
  apply Coprime.pow_left
  refine (coprime_or_dvd_of_prime pp k).elim id fun h ↦ absurd h ?_
  rw [← mul_dvd_mul_iff_left (pow_ne_zero s pp.ne_zero), ← Nat.pow_succ, ← hk]
  exact pow_succ_padicValNat_not_dvd (two_pos.trans_le hn).ne'
