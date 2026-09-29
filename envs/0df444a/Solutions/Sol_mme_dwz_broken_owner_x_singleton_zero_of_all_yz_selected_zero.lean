-- Prove2me | solution 1 for mme_dwz_broken_owner_x_singleton_zero_of_all_yz_selected_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T23:30:08.386017+00:00
-- url     : https://prove2.me/submissions/ca04a7cc-7920-4e36-b089-820f73d344e7

import Theorems.Thm_mme_basisZAllowed_map_eq_zero_of_selected_singletons
import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
import Definitions.Def_mme_dwz_step1_projector_basis_api

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open MME.DWZSourceAligned

/-- If every surviving Z word and every Y word kills a fixed X singleton,
then the complete Z mask and Y basis sum kill that X singleton. -/
theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (x : AddressModeWord outer 0)
    (hTripleZero : ∀ (y : AddressModeWord outer 1)
      (z : AddressZWord outer),
      addressWordSurvives m outer copy z →
      let G := brokenAddressGrading K m outer copy
      let sx := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 0) id {x}
      let sy := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 1) id {y}
      let sz := DWZComponentRestriction.basisLabelProjection
        (coarseAddressZBasis K outer) id {z}
      let selected : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K]
            (coarseAddressObj K outer).V i :=
        Function.update
          (Function.update
            (Function.update (fun _ ↦ LinearMap.id) 0 sx) 1 sy) 2 sz
      PiTensorProduct.map
        (fun i ↦ (G.blockProj i 0).comp (selected i))
        (coarseAddressObj K outer).t = 0) :
    let G := brokenAddressGrading K m outer copy
    let base : ∀ i : Fin 3,
        (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
      fun i ↦ G.blockProj i 0
    let sx := DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 0) id {x}
    PiTensorProduct.map
      (Function.update base 0 ((base 0).comp sx))
      (coarseAddressObj K outer).t = 0 := by
  classical
  dsimp only
  let T := coarseAddressObj K outer
  let G := brokenAddressGrading K m outer copy
  let sx : T.V 0 →ₗ[K] T.V 0 :=
    DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 0) id {x}
  let pre : ∀ i : Fin 3, T.V i →ₗ[K] T.V i :=
    Function.update (fun _ ↦ LinearMap.id) 0 sx
  have hZ := mme_basisZAllowed_map_eq_zero_of_selected_singletons
    (S := T) (T := T)
    (coarseAddressZBasis K outer)
    (addressWordSurvives m outer copy) pre
    (by
      intro z hz
      dsimp only
      let sz : T.V 2 →ₗ[K] T.V 2 :=
        DWZComponentRestriction.basisLabelProjection
          (coarseAddressZBasis K outer) id {z}
      let zMaps : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
        Function.update
          (fun i ↦ (G.blockProj i 0).comp (pre i)) 2
          (((G.blockProj 2 0).comp sz).comp (pre 2))
      apply mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
        (K := K) (d := 3) (S := T) (U := G.blockSubtensor (fun _ ↦ 0))
        1 (coarseAddressModeBasis K outer 1) (fun _ ↦ True)
        LinearMap.id (G.blockProj 1 0) zMaps
      · rfl
      · intro y hy
        exact (hy trivial).elim
      · intro y _hy
        dsimp only
        let sy : T.V 1 →ₗ[K] T.V 1 :=
          DWZComponentRestriction.basisLabelProjection
            (coarseAddressModeBasis K outer 1) id {y}
        let selected : ∀ i : Fin 3, T.V i →ₗ[K] T.V i :=
          Function.update
            (Function.update
              (Function.update (fun _ ↦ LinearMap.id) 0 sx) 1 sy) 2 sz
        have h := hTripleZero y z hz
        change PiTensorProduct.map
          (fun i ↦ (G.blockProj i 0).comp (selected i)) T.t = 0 at h
        have hmaps : Function.update zMaps 1
              (((G.blockProj 1 0).comp
                (DWZComponentRestriction.basisLabelProjection
                  (coarseAddressModeBasis K outer 1) id {y})).comp
                LinearMap.id) =
            (fun i ↦ (G.blockProj i 0).comp (selected i)) := by
          funext i
          fin_cases i <;> rfl
        exact (congrArg
          (fun maps ↦ PiTensorProduct.map maps T.t) hmaps).trans h)
  dsimp only at hZ
  change PiTensorProduct.map
    (fun i ↦ (G.blockProj i 0).comp (pre i)) T.t = 0 at hZ
  let base : ∀ i : Fin 3, T.V i →ₗ[K] G.classOf i 0 :=
    fun i ↦ G.blockProj i 0
  let xMaps := Function.update base 0 ((base 0).comp sx)
  have hmaps : (fun i ↦ (G.blockProj i 0).comp (pre i)) = xMaps := by
    funext i
    fin_cases i <;> rfl
  have htransport := congrArg
    (fun maps ↦ PiTensorProduct.map maps T.t) hmaps
  have hxMaps : PiTensorProduct.map xMaps T.t = 0 :=
    htransport.symm.trans hZ
  simpa only [T, G, base, sx, xMaps] using hxMaps
