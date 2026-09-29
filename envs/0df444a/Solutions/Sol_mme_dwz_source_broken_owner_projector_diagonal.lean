-- Prove2me | solution 1 for mme_dwz_source_broken_owner_projector_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T18:21:31.816288+00:00
-- url     : https://prove2.me/submissions/61903b8e-3e53-450d-9eb0-4c588d2afd76

import Theorems.Thm_mme_gradedAddressProj_then_blockProj_preserves_tensor
import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    PiTensorProduct.map
        (fun i ↦
          ((DWZSourceAligned.brokenAddressGrading K m outer copy).blockProj i 0).comp
            (gradedAddressProj (cwSquareCanonicalGrading K 6) N
              (DWZSourceAligned.coarseAddress outer) i))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t =
      (DWZSourceAligned.brokenAddressObj K m outer copy).t := by
  exact
    (mme_gradedAddressProj_then_blockProj_preserves_tensor
      (cwSquareCanonicalGrading K 6)
      (DWZSourceAligned.coarseAddress outer)
      (DWZSourceAligned.brokenAddressGrading K m outer copy)
      (fun _ ↦ 0))
