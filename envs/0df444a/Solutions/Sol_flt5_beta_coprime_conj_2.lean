-- Prove2me | solution 2 for flt5_beta_coprime_conj
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:41.591745+00:00
-- url     : https://prove2.me/submissions/ccd2ade3-6058-4272-bcc5-9431ca220e03

import Mathlib

private instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

private theorem nontrivial_fifth_cyclotomic_automorphism :
    ∃ σ : (CyclotomicField 5 ℚ) ≃ₐ[ℚ] (CyclotomicField 5 ℚ),
      σ ≠ AlgEquiv.refl := by
  let K := CyclotomicField 5 ℚ
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {5} ℚ K
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 4 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank 5 K]
    rw [Nat.totient_prime Nat.prime_five]
  by_contra h
  push Not at h
  let : Unique (K ≃ₐ[ℚ] K) := { default := AlgEquiv.refl, uniq := h }
  have hone : Nat.card (K ≃ₐ[ℚ] K) = 1 := Nat.card_unique
  omega

theorem solution : ¬ (∀ (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ))
    (hβ : Algebra.norm ℤ β = s ^ 5)
    (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))),
    ∀ σ : (CyclotomicField 5 ℚ) ≃ₐ[ℚ] (CyclotomicField 5 ℚ),
      σ ≠ AlgEquiv.refl →
      IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β)) := by
  intro h
  obtain ⟨σ, hσ⟩ := nontrivial_fifth_cyclotomic_automorphism
  have hbad := h 1 0 0 (by norm_num) 0 (by simp)
    (IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)) σ hσ
  obtain ⟨x, y, hxy⟩ := hbad
  simp at hxy

#check solution
#print axioms solution
