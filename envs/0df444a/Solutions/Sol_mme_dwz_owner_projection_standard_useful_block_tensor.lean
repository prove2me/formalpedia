-- Prove2me | solution 1 for mme_dwz_owner_projection_standard_useful_block_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:32:14.917442+00:00
-- url     : https://prove2.me/submissions/31b4099b-7ce0-426a-9d58-4102c2f7e10e

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_dwz_basis_label_owner_map_singleton

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m) {s : ℕ}
    (owner : DWZStandardBlock m → Fin s) (t : Fin s)
    (block : DWZStandardBlock m) :
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (basisLabelProjection D.basis D.label
            (Finset.univ.filter (fun b ↦ t = owner b))))
        (dwzLabelledUsefulBlockTensor K m D block) =
      if t = owner block then
        dwzLabelledUsefulBlockTensor K m D block
      else 0 := by
  rw [dwzLabelledUsefulBlockTensor]
  exact mme_dwz_basis_label_owner_map_singleton
    D.X D.basis D.label owner t block
