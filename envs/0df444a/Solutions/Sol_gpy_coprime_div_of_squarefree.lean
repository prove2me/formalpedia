-- Prove2me | solution 1 for gpy_coprime_div_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T23:11:37.852671+00:00
-- url     : https://prove2.me/submissions/553d736a-3d77-40e2-a150-06a6ed780ec0

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem sq_not_dvd_both_aux {n d : ℕ} (hsq : Squarefree n) (hd : d ∣ n)
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

theorem solution {n d : ℕ} (hsq : Squarefree n)
    (hd : d ∣ n) : Nat.Coprime (n / d) d := by
  show Nat.gcd (n / d) d = 1
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : p ∣ n / d := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  exact sq_not_dvd_both_aux hsq hd hp ⟨h2, h1⟩
