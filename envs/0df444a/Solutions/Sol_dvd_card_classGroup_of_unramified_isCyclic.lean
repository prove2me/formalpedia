-- Prove2me | solution 1 for dvd_card_classGroup_of_unramified_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:02.586874+00:00
-- url     : https://prove2.me/submissions/16207355-43c8-40d4-a24d-e02bd8ea42ab

module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Theorems.Thm_Ideal_isPrincipal_pow_finrank_of_isPrincipal_map
public import Theorems.Thm_exists_not_isPrincipal_and_isPrincipal_map
public import Theorems.Thm_Hilbert92


set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField
variable {K : Type} [Field K]
open Polynomial Module
variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]
variable [IsGalois K L]
theorem _root_.solution {K L : Type}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [IsCyclic (L ≃ₐ[K] L)] (hKL : Nat.Prime (finrank K L)) (hKL' : finrank K L ≠ 2) :
    finrank K L ∣ Fintype.card (ClassGroup (𝓞 K)) := by
  obtain ⟨I, hI, hI'⟩ := exists_not_isPrincipal_and_isPrincipal_map K L hKL hKL'
  have := Fact.mk hKL
  rw [hKL.dvd_iff_not_coprime]
  exact fun h ↦ hI (Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime h
    (Ideal.isPrincipal_pow_finrank_of_isPrincipal_map hI'))
