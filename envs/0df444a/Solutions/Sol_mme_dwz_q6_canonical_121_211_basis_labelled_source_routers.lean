-- Prove2me | solution 1 for mme_dwz_q6_canonical_121_211_basis_labelled_source_routers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:07:25.835893+00:00
-- url     : https://prove2.me/submissions/d76ff470-71f2-4383-b4c5-111ada664909

import Definitions.Def_mme_dwz_q6_grade_one_coord_data
import Theorems.Thm_mme_dwz_q6_grade_one_coord_leftGrade
import Theorems.Thm_mme_dwz_q6_canonical_121_basis_labelled_source_router
import Theorems.Thm_mme_dwz_q6_canonical_211_basis_labelled_source_router

open MME PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem solution
    (K : Type u) [Field K] :
    ∃ coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6),
      (∀ p,
        p.leftGrade =
          Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
            (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)) ∧
      (∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 1 2 1 s) →ₗ[K]
            (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
              (coupledObj K 6)).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 1 2 1)) =
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).t ∧
        ∀ p,
          maps 2 (canonicalComponentZBasis K (13 : Fin 15) p) =
            (Pi.single (coord p) 1 : (Fin 6 ⊕ Fin 6) → K)) ∧
      (∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 2 1 1 s) →ₗ[K]
            (TensorObj.permObj cyclicPerm (coupledObj K 6)).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 2 1 1)) =
          (TensorObj.permObj cyclicPerm (coupledObj K 6)).t ∧
        ∀ p,
          maps 2 (canonicalComponentZBasis K (14 : Fin 15) p) =
            (Pi.single (coord p) 1 : (Fin 6 ⊕ Fin 6) → K)) := by
  refine ⟨dwzQ6GradeOneCoord, mme_dwz_q6_grade_one_coord_leftGrade, ?_, ?_⟩
  · exact mme_dwz_q6_canonical_121_basis_labelled_source_router K
  · exact mme_dwz_q6_canonical_211_basis_labelled_source_router K
