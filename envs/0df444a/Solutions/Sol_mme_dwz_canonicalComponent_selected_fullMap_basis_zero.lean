-- Prove2me | solution 1 for mme_dwz_canonicalComponent_selected_fullMap_basis_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T09:30:00.451403+00:00
-- url     : https://prove2.me/submissions/02a65127-01c7-4541-ba4b-6553c0f77040

import Definitions.Def_mme_dwz_step1_source_address_projectors
import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Theorems.Thm_mme_dwz_coarseClassBasis_q6_val

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem componentModeBasis_coe
    {K : Type u} [Field K] (s : Fin 15) (i : Fin 3)
    (p : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (cwSquareBlockType
        (MME.DWZSquare.shapeX s)
        (MME.DWZSquare.shapeY s)
        (MME.DWZSquare.shapeZ s) i)) :
    (canonicalComponentModeBasis K s i p).1 =
      cwSquareCanonicalBasis K 6 i p.down.1 := by
  have hr : canonicalComponentModeBasis K s i p =
      MME.DWZComponentRestriction.coarseClassBasis (K := K) 6 i
        (cwSquareBlockType
          (MME.DWZSquare.shapeX s)
          (MME.DWZSquare.shapeY s)
          (MME.DWZSquare.shapeZ s) i) p.down := by
    exact Module.Basis.reindex_apply
      (MME.DWZComponentRestriction.coarseClassBasis (K := K) 6 i
        (cwSquareBlockType
          (MME.DWZSquare.shapeX s)
          (MME.DWZSquare.shapeY s)
          (MME.DWZSquare.shapeZ s) i)) Equiv.ulift.symm p
  rw [hr]
  exact mme_dwz_coarseClassBasis_q6_val K i
    (cwSquareBlockType
      (MME.DWZSquare.shapeX s)
      (MME.DWZSquare.shapeY s)
      (MME.DWZSquare.shapeZ s) i) p.down

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
    (i : Fin 3) (p : Fin 8 × Fin 8)
    (hp : p ≠ (selected i).down.1) :
    post i
        (MME.DWZComponentRestriction.basisLabelProjection
          (canonicalComponentModeBasis K s i) id {selected i}
          ((cwSquareCanonicalGrading K 6).blockProj i
            (cwSquareBlockType
              (MME.DWZSquare.shapeX s)
              (MME.DWZSquare.shapeY s)
              (MME.DWZSquare.shapeZ s) i)
            (cwSquareCanonicalBasis K 6 i p))) = 0 := by
  let c : Fin 5 := cwSquareBlockType
    (MME.DWZSquare.shapeX s)
    (MME.DWZSquare.shapeY s)
    (MME.DWZSquare.shapeZ s) i
  change post i
      (MME.DWZComponentRestriction.basisLabelProjection
        (canonicalComponentModeBasis K s i) id {selected i}
        ((cwSquareCanonicalGrading K 6).blockProj i c
          (cwSquareCanonicalBasis K 6 i p))) = 0
  by_cases hc : cwSquarePairGrade 6 p = c
  · have hmem : cwSquareCanonicalBasis K 6 i p ∈
        (cwSquareCanonicalGrading K 6).classOf i c := by
      exact Submodule.subset_span ⟨p, hc, rfl⟩
    let lifted : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6 c :=
      ULift.up ⟨p, hc⟩
    have hvec :
        (⟨cwSquareCanonicalBasis K 6 i p, hmem⟩ :
          (cwSquareCanonicalGrading K 6).classOf i c) =
        canonicalComponentModeBasis K s i lifted := by
      apply Subtype.ext
      exact (componentModeBasis_coe (K := K) s i lifted).symm
    have hlifted : lifted ≠ selected i := by
      intro h
      apply hp
      exact congrArg (fun z ↦ z.down.1) h
    rw [TensorObj.TypeGrading.blockProj_apply_mem
      (cwSquareCanonicalGrading K 6) i c
      (cwSquareCanonicalBasis K 6 i p) hmem, hvec]
    simp only [MME.DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
      if_neg hlifted, map_zero]
  · have hmem : cwSquareCanonicalBasis K 6 i p ∈
        (cwSquareCanonicalGrading K 6).classOf i
          (cwSquarePairGrade 6 p) := by
      exact Submodule.subset_span ⟨p, rfl, rfl⟩
    rw [TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwSquareCanonicalGrading K 6) i c
      (cwSquarePairGrade 6 p) (Ne.symm hc)
      (cwSquareCanonicalBasis K 6 i p) hmem]
    have hinner :
        MME.DWZComponentRestriction.basisLabelProjection
          (canonicalComponentModeBasis K s i) id {selected i} 0 = 0 :=
      LinearMap.map_zero _
    calc
      post i
          (MME.DWZComponentRestriction.basisLabelProjection
            (canonicalComponentModeBasis K s i) id {selected i} 0) =
          post i 0 := congrArg (fun x ↦ post i x) hinner
      _ = 0 := LinearMap.map_zero _
