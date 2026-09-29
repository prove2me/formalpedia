-- Prove2me | solution 1 for mme_primary_hash_family_permuted_outer_extraction_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:59:43.558511+00:00
-- url     : https://prove2.me/submissions/26a87383-c4d9-4286-be51-3138b820c15c

import Theorems.Thm_mme_perm_kronPow_mode_equiv_preserves_tensor
import Theorems.Thm_mme_primary_hash_family_sharedZ_outer_extraction_exact

open MME MME.TensorObj PiTensorProduct BigOperators
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (e : Equiv.Perm (Fin 3)) :
    PiTensorProduct.map
        (fun i ↦ (outerExtractionMap grading family (e.symm i)).comp
          (TensorObj.permKronPowModeEquiv e T i (2 * N)).toLinearMap)
        ((TensorObj.permObj e T).kronPow (2 * N)).t =
      (TensorObj.permObj e
        (TensorObj.bigAdd (starObj grading family))).t := by
  have hbase :=
    (mme_primary_hash_family_sharedZ_outer_extraction_exact
      grading family hSupport).1
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  rw [mme_perm_kronPow_mode_equiv_preserves_tensor]
  change PiTensorProduct.map
      (fun i ↦ outerExtractionMap grading family (e.symm i))
      (PiTensorProduct.reindex K (T.kronPow (2 * N)).V e
        (T.kronPow (2 * N)).t) = _
  rw [PiTensorProduct.map_reindex, hbase]
