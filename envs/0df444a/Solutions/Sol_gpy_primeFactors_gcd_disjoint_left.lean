-- Prove2me | solution 1 for gpy_primeFactors_gcd_disjoint_left
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T01:58:28.44938+00:00
-- url     : https://prove2.me/submissions/3a2bec42-71f5-4c90-94f2-a19c523153f3

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

theorem solution {D E : ℕ} (hsqD : Squarefree D) :
    Disjoint (Nat.gcd D E).primeFactors (D / Nat.gcd D E).primeFactors := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [Nat.mem_primeFactors] at hp1 hp2
  exact sq_not_dvd_both_aux hsqD (Nat.gcd_dvd_left D E) hp1.1 ⟨hp1.2.1, hp2.2.1⟩
