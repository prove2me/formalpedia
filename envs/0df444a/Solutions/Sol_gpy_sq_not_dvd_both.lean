-- Prove2me | solution 1 for gpy_sq_not_dvd_both
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T22:56:04.156201+00:00
-- url     : https://prove2.me/submissions/1be36ff0-0c99-4bab-9bad-6763dfbdb126

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution {n d : ℕ} (hsq : Squarefree n) (hd : d ∣ n)
    {p : ℕ} (hp : p.Prime) : ¬ (p ∣ d ∧ p ∣ n / d) := by
  rintro ⟨h1, h2⟩
  have hpp : p * p ∣ n := by
    have hnm : n = (n / d) * d := (Nat.div_mul_cancel hd).symm
    rw [hnm]
    exact mul_dvd_mul h2 h1
  have hunit : IsUnit p := hsq p hpp
  rw [Nat.isUnit_iff] at hunit
  subst hunit
  exact Nat.not_prime_one hp
