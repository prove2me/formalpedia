-- Prove2me | solution 1 for syracuse_periodic_reaches_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:44:06.665345+00:00
-- url     : https://prove2.me/submissions/82ad6657-2c4d-40fb-ad6e-d88eab89d84c

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem stepEq (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem T1 : syracuseStep 1 = 1 := stepEq 2 (by norm_num) (by decide)

theorem iter1 : ∀ j : ℕ, syracuseStep^[j] 1 = 1 := by
  intro j
  induction j with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, T1]

theorem solution (z a : ℕ) (ha : 0 < a) (hcyc : syracuseStep^[a] z = z)
    (hreach : ∃ k : ℕ, syracuseStep^[k] z = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hreach
  -- the cycle repeats at every multiple of its length
  have hper : ∀ m : ℕ, syracuseStep^[a * m] z = z := by
    intro m
    induction m with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, Function.iterate_add_apply, hcyc]; exact ih
  -- run past the point where the orbit has already reached 1
  have hz : z = syracuseStep^[a * k - k] (syracuseStep^[k] z) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k ha)]
    exact (hper k).symm
  rw [hk, iter1] at hz
  exact hz
