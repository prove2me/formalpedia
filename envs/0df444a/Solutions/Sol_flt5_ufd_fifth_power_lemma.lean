-- Prove2me | solution 1 for flt5_ufd_fifth_power_lemma
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-14T07:47:49.292362+00:00
-- url     : https://prove2.me/submissions/10293344-68bc-4cdf-9516-2725b499ff26

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

noncomputable section

open NumberField

abbrev CK5ufd := CyclotomicField 5 ℚ
abbrev ZZ5ufd := NumberField.RingOfIntegers CK5ufd

instance : IsCyclotomicExtension {5} ℚ CK5ufd :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5ufd :=
  IsCyclotomicExtension.numberField {5} ℚ CK5ufd

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : IsGalois ℚ CK5ufd :=
  IsCyclotomicExtension.isGalois {5} ℚ CK5ufd

lemma mapAlgEquiv_coe_ufd (σ : CK5ufd ≃ₐ[ℚ] CK5ufd) (β : ZZ5ufd) :
    ((RingOfIntegers.mapAlgEquiv σ β : ZZ5ufd) : CK5ufd) = σ ((β : ZZ5ufd) : CK5ufd) :=
  RingOfIntegers.mapRingHom_apply σ.toRingHom β

lemma mapAlgEquiv_refl_ufd (β : ZZ5ufd) :
    RingOfIntegers.mapAlgEquiv (AlgEquiv.refl : CK5ufd ≃ₐ[ℚ] CK5ufd) β = β := by
  apply RingOfIntegers.coe_injective (K := CK5ufd)
  simp [mapAlgEquiv_coe_ufd]

lemma norm_galois_prod_ufd (β : ZZ5ufd) :
    algebraMap ℤ ZZ5ufd (Algebra.norm ℤ β) =
    ∏ σ : CK5ufd ≃ₐ[ℚ] CK5ufd, RingOfIntegers.mapAlgEquiv σ β := by
  apply RingOfIntegers.coe_injective (K := CK5ufd)
  simp_rw [map_prod, mapAlgEquiv_coe_ufd]
  rw [← Algebra.norm_eq_prod_automorphisms (K := ℚ) (L := CK5ufd)]
  rw [← Algebra.coe_norm_int (K := CK5ufd)]
  simp [map_intCast]

theorem solution (hPID : IsPrincipalIdealRing ZZ5ufd) (β : ZZ5ufd) (s : ℤ)
    (hβ : Algebra.norm ℤ β = s ^ 5)
    (hcop : ∀ σ : CK5ufd ≃ₐ[ℚ] CK5ufd, σ ≠ AlgEquiv.refl →
        IsCoprime β (RingOfIntegers.mapAlgEquiv σ β)) :
    ∃ (u : ZZ5ufd ˣ) (d : ZZ5ufd), β = (u : ZZ5ufd) * d ^ 5 := by
  haveI := hPID
  haveI : IsBezout ZZ5ufd := inferInstance
  haveI : DecidableEq (CK5ufd ≃ₐ[ℚ] CK5ufd) := Classical.decEq _
  have hnorm : algebraMap ℤ ZZ5ufd (Algebra.norm ℤ β) =
      ∏ σ : CK5ufd ≃ₐ[ℚ] CK5ufd, RingOfIntegers.mapAlgEquiv σ β :=
    norm_galois_prod_ufd β
  rw [hβ, map_pow] at hnorm
  have hmem : AlgEquiv.refl ∈ Finset.univ (α := CK5ufd ≃ₐ[ℚ] CK5ufd) := Finset.mem_univ _
  rw [← Finset.mul_prod_erase _ _ hmem, mapAlgEquiv_refl_ufd] at hnorm
  let rest := ∏ σ ∈ Finset.univ.erase (AlgEquiv.refl : CK5ufd ≃ₐ[ℚ] CK5ufd),
      RingOfIntegers.mapAlgEquiv σ β
  have hcop' : IsCoprime β rest :=
    IsCoprime.prod_right_iff.mpr fun σ hσ => hcop σ (Finset.ne_of_mem_erase hσ)
  have hpow : β * rest = (algebraMap ℤ ZZ5ufd s) ^ 5 := hnorm.symm
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcop' hpow
  obtain ⟨u, hu⟩ := hd
  exact ⟨u, d, by rw [← hu, mul_comm]⟩

end
