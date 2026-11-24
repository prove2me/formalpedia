-- Prove2me | solution 1 for exists_not_isPrincipal_and_isPrincipal_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:05.051806+00:00
-- url     : https://prove2.me/submissions/8f12da16-336f-4dfb-9b3b-013d25a9ab23

module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Theorems.Thm_exists_not_isPrincipal_and_isPrincipal_map_aux
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
theorem _root_.solution (K L : Type)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [h : IsCyclic (L ≃ₐ[K] L)] (hKL : Nat.Prime (finrank K L)) (hKL' : finrank K L ≠ 2) :
    ∃ I : Ideal (𝓞 K), ¬I.IsPrincipal ∧
      (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  obtain ⟨⟨σ, hσ⟩⟩ := h
  obtain ⟨η, hη, hη'⟩ := Hilbert92 hKL hKL' σ hσ
  exact exists_not_isPrincipal_and_isPrincipal_map_aux σ hσ η hη (not_exists.mpr hη')
