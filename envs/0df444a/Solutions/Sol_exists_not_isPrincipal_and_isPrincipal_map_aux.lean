-- Prove2me | solution 1 for exists_not_isPrincipal_and_isPrincipal_map_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:59.64122+00:00
-- url     : https://prove2.me/submissions/f0b8eacb-112d-40db-a0e2-86fcb4bbb122

module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Theorems.Thm_comap_span_galRestrict_eq_of_cyclic
public import Theorems.Thm_Hilbert92
public import Theorems.Thm_comap_map_eq_of_unramified


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
include hσ
open FiniteDimensional
theorem _root_.solution
    [IsDedekindDomain A] [Algebra.Unramified A B] (η : Bˣ)
    (hη : Algebra.norm K (algebraMap B L η) = 1)
    (hη' : ¬∃ α : Bˣ, algebraMap B L η = (algebraMap B L α) / σ (algebraMap B L α)) :
    ∃ I : Ideal A, ¬I.IsPrincipal ∧ (I.map (algebraMap A B)).IsPrincipal := by
  have := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ, (Subgroup.eq_top_iff' _).2 hσ⟩
  obtain ⟨β, hβ_zero, hβ⟩ := groupCohomology.exists_mul_galRestrict_of_norm_eq_one (A := A)
    (B := B) hσ hη
  have : IsDomain B := Function.Injective.isDomain _ (IsIntegralClosure.algebraMap_injective B A L)
  have hβ' := comap_map_eq_of_unramified K L _
    (comap_span_galRestrict_eq_of_cyclic σ hσ (A := A) (B := B) β η hβ)
  refine ⟨(Ideal.span {β}).comap (algebraMap A B), ?_, ?_⟩
  · rintro ⟨⟨γ, hγ : _ = Ideal.span _⟩⟩
    rw [hγ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hβ'
    obtain ⟨a, rfl⟩ := hβ'
    rw [map_mul, AlgEquiv.commutes, mul_left_comm, (mul_right_injective₀ _).eq_iff] at hβ
    · apply hη'
      use a
      conv_rhs =>
        enter [1]
        rw [← hβ]
      rw [map_mul, ← algebraMap_galRestrict_apply A]
      refine (mul_div_cancel_right₀ _ ?_).symm
      · rw [ne_eq,
          (injective_iff_map_eq_zero' _).mp (IsIntegralClosure.algebraMap_injective B A L),
          (injective_iff_map_eq_zero' _).mp (galRestrict A K L B σ).injective]
        exact a.isUnit.ne_zero
    · exact (mul_ne_zero_iff.mp hβ_zero).1
  · rw [hβ']
    exact ⟨⟨_, rfl⟩⟩
