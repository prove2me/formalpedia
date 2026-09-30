-- Prove2me | solution 1 for polynomial_goldbach_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:23:22.576325+00:00
-- url     : https://prove2.me/submissions/d06531d4-328d-41e1-aedc-f5711dc8fd7f

import Mathlib

open Polynomial

private theorem eisenstein_extension (p : Polynomial ℤ) (a c ell : ℤ)
    (hell : Prime ell) (ha : ell ∣ a) (hc : ell ∣ c)
    (hconstant : ¬ ell ^ 2 ∣ a * p.coeff 0 + c) :
    Irreducible (X ^ (p.natDegree + 1) + (C a * p + C c)) := by
  let f := X ^ (p.natDegree + 1) + (C a * p + C c)
  have hsmall : (C a * p + C c).natDegree < p.natDegree + 1 := by
    apply lt_of_le_of_lt (natDegree_add_le _ _)
    simp only [max_lt_iff, natDegree_C]
    exact ⟨lt_of_le_of_lt (natDegree_C_mul_le _ _) (Nat.lt_succ_self _),
      Nat.succ_pos _⟩
  have hfdeg : f.natDegree = p.natDegree + 1 := by
    simpa only [f, natDegree_X_pow] using
      (natDegree_add_eq_left_of_natDegree_lt
        (p := (X : Polynomial ℤ) ^ (p.natDegree + 1))
        (q := C a * p + C c) (by simpa only [natDegree_X_pow] using hsmall))
  have hfmonic : f.Monic := by
    apply monic_X_pow_add
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hsmall)
  have hprime : (Ideal.span ({ell} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hell.ne_zero).mpr hell
  have heisen : f.IsEisensteinAt (Ideal.span ({ell} : Set ℤ)) := by
    apply hfmonic.isEisensteinAt_of_mem_of_notMem hprime.ne_top
    · intro k hk
      rw [hfdeg] at hk
      apply Ideal.mem_span_singleton.mpr
      dsimp [f]
      simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C]
      rw [if_neg (Nat.ne_of_lt hk)]
      simp only [zero_add]
      apply dvd_add (dvd_mul_of_dvd_left ha _)
      split_ifs
      · exact hc
      · exact dvd_zero _
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simpa [f, coeff_add, coeff_X_pow, coeff_C_mul] using hconstant
  exact heisen.irreducible hprime hfmonic.isPrimitive (by rw [hfdeg]; omega)

private theorem decomposition_for_constant (p : Polynomial ℤ) (c : ℤ)
    (hc2 : (2 : ℤ) ∣ c) (hc3 : (3 : ℤ) ∣ c)
    (hc4 : ¬ (4 : ℤ) ∣ 4 * p.coeff 0 + c)
    (hc9 : ¬ (9 : ℤ) ∣ 3 * p.coeff 0 + c) :
    ∃ q r : Polynomial ℤ, Irreducible q ∧ Irreducible r ∧ p = q + r := by
  let q : Polynomial ℤ := X ^ (p.natDegree + 1) + (C 4 * p + C c)
  let t : Polynomial ℤ := X ^ (p.natDegree + 1) + (C 3 * p + C c)
  have hq : Irreducible q := eisenstein_extension p 4 c 2 (by norm_num)
    (by norm_num) hc2 (by simpa using hc4)
  have ht : Irreducible t := eisenstein_extension p 3 c 3 (by norm_num)
    (by norm_num) hc3 (by simpa using hc9)
  have hneg : Irreducible (-t) := by
    simpa using (irreducible_isUnit_mul (show IsUnit (-1 : Polynomial ℤ) from
      isUnit_neg_one)).mpr ht
  refine ⟨q, -t, hq, hneg, ?_⟩
  dsimp [q, t]
  norm_num only [map_ofNat]
  ring

theorem solution (p : Polynomial ℤ)
    (hdeg : 2 ≤ p.natDegree)
    (hirr : Irreducible p)
    (hlc : 0 < p.leadingCoeff) :
    ∃ (q r : Polynomial ℤ),
      Irreducible q ∧ Irreducible r ∧ p = q + r := by
  by_cases h : (9 : ℤ) ∣ 3 * p.coeff 0 + 6
  · apply decomposition_for_constant p 18 (by norm_num) (by norm_num)
    · intro hdiv
      have := Int.emod_eq_zero_of_dvd hdiv
      omega
    · intro hdiv
      have hmod := Int.emod_eq_zero_of_dvd h
      have hmod' := Int.emod_eq_zero_of_dvd hdiv
      omega
  · apply decomposition_for_constant p 6 (by norm_num) (by norm_num) _ h
    intro hdiv
    have := Int.emod_eq_zero_of_dvd hdiv
    omega

#check solution
#print axioms solution
