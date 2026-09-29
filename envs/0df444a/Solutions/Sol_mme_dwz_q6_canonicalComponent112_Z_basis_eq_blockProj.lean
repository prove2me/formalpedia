-- Prove2me | solution 1 for mme_dwz_q6_canonicalComponent112_Z_basis_eq_blockProj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T19:20:47.824963+00:00
-- url     : https://prove2.me/submissions/191e2475-84ed-4afb-a5db-dc6b95c309a1

import Theorems.Thm_mme_dwz_coarseClassBasis_q6_val
import Definitions.Def_mme_TypeGrading_kron

open MME Module MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem solution
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 2) :
    canonicalComponentZBasis K 12 p =
      (cwSquareCanonicalGrading K 6).blockProj 2 2
        (cwSquareCanonicalBasis K 6 2 p.down.1) := by
  apply Subtype.ext
  rw [TensorObj.TypeGrading.blockProj_apply_mem]
  · have hr :
        canonicalComponentZBasis K 12 p =
          coarseClassBasis (K := K) 6 2
            (MME.DWZSquare.shapeZ 12) p.down := by
      exact Module.Basis.reindex_apply
        (coarseClassBasis (K := K) 6 2
          (MME.DWZSquare.shapeZ 12)) Equiv.ulift.symm p
    rw [hr]
    exact mme_dwz_coarseClassBasis_q6_val K 2 2 p.down
  · exact Submodule.subset_span ⟨p.down.1, p.down.2, rfl⟩
