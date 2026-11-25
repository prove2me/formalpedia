-- Prove2me | solution 1 for twin_primes_coprime
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:23:08.911395+00:00
-- url     : https://prove2.me/submissions/2facff71-e930-4fd3-9c27-ae07889bf4e8

import Mathlib

theorem solution (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) : p.Coprime (p + 2) := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have hdvd2 : p ∣ 2 := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · rw [h] at hp
    exact absurd hp Nat.not_prime_one
  · rw [h] at hp2
    exact absurd hp2 (by decide)
