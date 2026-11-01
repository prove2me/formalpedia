-- Prove2me | solution 1 for gpy_primeFactors_gcd_disjoint_right
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T02:27:57.046977+00:00
-- url     : https://prove2.me/submissions/347a13b4-7bdc-4f18-9c6f-a01d196ab867

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

theorem solution {D E : ℕ} (hsqD : Squarefree D)
    (hsqE : Squarefree E) :
    Disjoint ((Nat.gcd D E).primeFactors ∪ (D / Nat.gcd D E).primeFactors)
      (E / Nat.gcd D E).primeFactors := by
  rw [Finset.disjoint_left]
  intro p hpU hpE
  simp only [Finset.mem_union, Nat.mem_primeFactors] at hpU
  rw [Nat.mem_primeFactors] at hpE
  rcases hpU with hp1 | hp1
  · exact sq_not_dvd_both_aux hsqE (Nat.gcd_dvd_right D E) hp1.1 ⟨hp1.2.1, hpE.2.1⟩
  · have hpD : p ∣ D :=
      dvd_trans hp1.2.1 ⟨Nat.gcd D E, (Nat.div_mul_cancel (Nat.gcd_dvd_left D E)).symm⟩
    have hpE' : p ∣ E :=
      dvd_trans hpE.2.1 ⟨Nat.gcd D E, (Nat.div_mul_cancel (Nat.gcd_dvd_right D E)).symm⟩
    have hpg : p ∣ Nat.gcd D E := Nat.dvd_gcd hpD hpE'
    exact sq_not_dvd_both_aux hsqD (Nat.gcd_dvd_left D E) hp1.1 ⟨hpg, hp1.2.1⟩
