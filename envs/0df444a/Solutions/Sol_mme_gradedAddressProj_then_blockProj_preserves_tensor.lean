-- Prove2me | solution 1 for mme_gradedAddressProj_then_blockProj_preserves_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T18:14:38.337041+00:00
-- url     : https://prove2.me/submissions/3980b76c-f529-4d11-b35d-fbc08d1e35ee

import Theorems.Thm_mme_gradedAddressProj_preserves_kronPow_tensor
import Definitions.Def_mme_block_subtensor

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t R q : ℕ}
    (G : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t)
    (H : (gradedAddressBlock G address).TypeGrading q)
    (sigma : Fin 3 → Fin q) :
    PiTensorProduct.map
        (fun i ↦ (H.blockProj i (sigma i)).comp
          (gradedAddressProj G R address i))
        (T.kronPow R).t =
      (H.blockSubtensor sigma).t := by
  rw [PiTensorProduct.map_comp]
  change PiTensorProduct.map (fun i ↦ H.blockProj i (sigma i))
      (PiTensorProduct.map (gradedAddressProj G R address)
        (T.kronPow R).t) = _
  rw [mme_gradedAddressProj_preserves_kronPow_tensor]
  rfl
