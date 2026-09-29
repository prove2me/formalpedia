-- Prove2me | solution 1 for mme_dwz_canonicalComponent_selected_fullMap_zero_of_fine_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T09:56:58.088139+00:00
-- url     : https://prove2.me/submissions/376cc56c-0c23-4dcd-a427-cfdb9fea8a32

import Definitions.Def_mme_dwz_step1_source_address_projectors
import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Theorems.Thm_mme_cwSquare_canonical_singleton_postmap_eq_zero_of_fine_block
import Theorems.Thm_mme_dwz_canonicalComponent_selected_fullMap_factor

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K] (s : Fin 15)
    (selected : ∀ i : Fin 3,
      MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (cwSquareBlockType
          (MME.DWZSquare.shapeX s)
          (MME.DWZSquare.shapeY s)
          (MME.DWZSquare.shapeZ s) i))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      (MME.DWZComponentRestriction.canonicalComponentBlock K s).V i →ₗ[K]
        W i)
    (hzero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (selected i).leftGrade (selected i).rightGrade) = 0) :
    PiTensorProduct.map
        (fun i ↦ ((post i).comp
          (MME.DWZComponentRestriction.basisLabelProjection
            (canonicalComponentModeBasis K s i) id {selected i})).comp
          ((cwSquareCanonicalGrading K 6).blockProj i
            (cwSquareBlockType
              (MME.DWZSquare.shapeX s)
              (MME.DWZSquare.shapeY s)
              (MME.DWZSquare.shapeZ s) i)))
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).t = 0 := by
  let actual : ∀ _ : Fin 3, Fin 8 × Fin 8 :=
    fun i ↦ (selected i).down.1
  let fullMaps : ∀ i : Fin 3,
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i) →ₗ[K] W i :=
    fun i ↦ ((post i).comp
      (MME.DWZComponentRestriction.basisLabelProjection
        (canonicalComponentModeBasis K s i) id {selected i})).comp
      ((cwSquareCanonicalGrading K 6).blockProj i
        (cwSquareBlockType
          (MME.DWZSquare.shapeX s)
          (MME.DWZSquare.shapeY s)
          (MME.DWZSquare.shapeZ s) i))
  have hfine : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (cwSquareCoordGrade 6 (actual i).1)
        (cwSquareCoordGrade 6 (actual i).2)) = 0 := by
    exact hzero
  have hcw := mme_cwSquare_canonical_singleton_postmap_eq_zero_of_fine_block
    (K := K) 6 actual fullMaps hfine
  have hfamilies :
      (fun i ↦ (fullMaps i).comp
        (MME.DWZComponentRestriction.basisLabelProjection
          (cwSquareCanonicalBasis K 6 i) id {actual i})) = fullMaps := by
    funext i
    simpa only [fullMaps, actual] using
      mme_dwz_canonicalComponent_selected_fullMap_factor
        (K := K) s selected post i
  rw [hfamilies] at hcw
  exact hcw
