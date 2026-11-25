-- Prove2me | solution 1 for prime_triplet_unique
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:23:13.667503+00:00
-- url     : https://prove2.me/submissions/278b28b7-e88f-4f23-b2fb-0359bc17bfd0

import Mathlib

theorem solution (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hp4 : (p + 4).Prime) :
    p = 3 := by
  have trich : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases trich with h | h | h
  · have hdvd : (3:ℕ) ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h
    rcases (Nat.dvd_prime hp).mp hdvd with habs | heq
    · exact absurd habs (by decide)
    · exact heq.symm
  · have hmod : (p + 2) % 3 = 0 := by omega
    have hdvd : (3:ℕ) ∣ p + 2 := Nat.dvd_iff_mod_eq_zero.mpr hmod
    rcases (Nat.dvd_prime hp2).mp hdvd with habs | heq
    · exact absurd habs (by decide)
    · have hp1 : p = 1 := by omega
      rw [hp1] at hp
      exact absurd hp Nat.not_prime_one
  · have hmod : (p + 4) % 3 = 0 := by omega
    have hdvd : (3:ℕ) ∣ p + 4 := Nat.dvd_iff_mod_eq_zero.mpr hmod
    rcases (Nat.dvd_prime hp4).mp hdvd with habs | heq
    · exact absurd habs (by decide)
    · omega
