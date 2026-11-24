-- Prove2me | solution 1 for exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:47.244814+00:00
-- url     : https://prove2.me/submissions/31264c93-399d-469a-a4b6-c625cae2f98f

module
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_KummersLemma
public import Theorems.Thm_KummersLemma_isUnramified
public import Theorems.Thm_dvd_card_classGroup_of_unramified_isCyclic


set_option autoImplicit false
@[expose] public section
public section
open Polynomial IsCyclotomicExtension.Rat
open scoped NumberField
variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)
include hp hreg
theorem _root_.solution {u : (𝓞 K)ˣ}
    (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (u : 𝓞 K) - 1) : ∃ v : K, v ^ p = u := by
  by_contra! hu
  have hirr := X_pow_sub_C_irreducible_of_prime hpri.out hu
  have := Fact.mk hirr
  let L := AdjoinRoot (X ^ p - C (u : K))
  have := isSplittingField_AdjoinRoot_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr
  have := isGalois_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have := IsSplittingField.finiteDimensional L (X ^ p - C (u : K))
  have := isCyclic_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : FiniteDimensional ℚ L := Module.Finite.trans K L
  have : NumberField L := ⟨⟩
  have hKL : Module.finrank K L = p :=
    finrank_of_isSplittingField_X_pow_sub_C
      ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have := KummersLemma.isUnramified hp hζ u hcong hu L
  have := dvd_card_classGroup_of_unramified_isCyclic (hKL.symm ▸ hpri.out) (hKL.symm ▸ hp)
  rw [hKL, hpri.out.dvd_iff_not_coprime] at this
  exact this (by convert hreg)
