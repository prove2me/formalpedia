-- Prove2me | solution 1 for mme_dwz_restricted_component_Z_position_shuffle_inclusion_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:18:46.309914+00:00
-- url     : https://prove2.me/submissions/22726762-492d-42fa-8d1d-64960448ef97

import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Theorems.Thm_mme_dwz_restricted_component_Z_position_shuffle
import Theorems.Thm_mme_kronPow_position_permutation_recursive_basis

open MME MME.TensorObj Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

theorem solution
    {K : Type u} [Field K]
    (s : Fin 15) (m : ℕ)
    (e : Equiv.Perm
      (Fin (MME.DWZTable2Counts.component s * m))) :
    ∃ E :
        (MME.DWZComponentRestriction.restrictedComponentPower K s m).V 2 ≃ₗ[K]
          (MME.DWZComponentRestriction.restrictedComponentPower K s m).V 2,
      (Submodule.subtype
          ((MME.DWZComponentRestriction.componentPowerProjectionGrading
            K s m).classOf 2 0)).comp E.toLinearMap =
        (kronPowModePositionEquiv
          (MME.DWZComponentRestriction.canonicalComponentBlock K s) 2
          (MME.DWZComponentRestriction.canonicalComponentZBasis K s)
          (MME.DWZTable2Counts.component s * m) e).toLinearMap.comp
          (Submodule.subtype
            ((MME.DWZComponentRestriction.componentPowerProjectionGrading
              K s m).classOf 2 0)) := by
  open MME.DWZComponentRestriction in
    rcases mme_dwz_restricted_component_Z_position_shuffle
        (K := K) s m e with ⟨E, hE⟩
  refine ⟨E, ?_⟩
  let b := MME.DWZComponentRestriction.componentPowerZBasis K s m
  let allowed := MME.DWZComponentRestriction.componentWordAllowed s m
  let C :=
    (MME.DWZComponentRestriction.componentPowerProjectionGrading K s m).classOf 2 0
  let Pspan := Submodule.span K (b '' {w | allowed w})
  have hZ : C = Pspan := by
    exact (mme_dwz_table2_component_projection_certificate
      (K := K) s m).2.2.2
  let castZ : C ≃ₗ[K] Pspan := LinearEquiv.ofEq _ _ hZ
  let v : MME.DWZComponentRestriction.AvailableComponentWord.{u} s m →
      (((MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
        (MME.DWZTable2Counts.component s * m)).V 2) :=
    fun w ↦ b w.1
  have hv : LinearIndependent K v := by
    exact b.linearIndependent.comp
      (fun w : MME.DWZComponentRestriction.AvailableComponentWord.{u} s m ↦ w.1)
      Subtype.val_injective
  have hrange : Set.range v = b '' {w | allowed w} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hspan : Submodule.span K (Set.range v) = Pspan := by
    rw [hrange]
  let bP : Basis
      (MME.DWZComponentRestriction.AvailableComponentWord.{u} s m) K Pspan :=
    (Basis.span hv).map (LinearEquiv.ofEq _ _ hspan)
  let bC : Basis
      (MME.DWZComponentRestriction.AvailableComponentWord.{u} s m) K C :=
    bP.map castZ.symm
  apply bC.ext
  intro w
  have hwC : b w.1 ∈ C := by
    rw [hZ]
    exact Submodule.subset_span ⟨w.1, w.2, rfl⟩
  have hbC : bC w = ⟨b w.1, hwC⟩ := by
    apply Subtype.ext
    simp only [bC, bP, Basis.map_apply]
    simp only [castZ]
    change
      ((LinearEquiv.ofEq _ _ hspan (Basis.span hv w) : Pspan) : _) =
        b w.1
    rw [LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]
  rw [hbC]
  change (E ⟨b w.1, hwC⟩).1 = _
  rw [hE w.1 w.2]
  exact (mme_kronPow_position_permutation_recursive_basis
    (MME.DWZComponentRestriction.canonicalComponentBlock K s) 2
    (MME.DWZComponentRestriction.canonicalComponentZBasis K s)
    (MME.DWZTable2Counts.component s * m) e w.1).symm
