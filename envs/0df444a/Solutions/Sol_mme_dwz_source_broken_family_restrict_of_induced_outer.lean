-- Prove2me | solution 1 for mme_dwz_source_broken_family_restrict_of_induced_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:45:49.848116+00:00
-- url     : https://prove2.me/submissions/7e7a1be9-9281-4d1e-b0f3-8df8b526d370

import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_dwz_source_aligned_broken_address_projection_certificate
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        (MME.cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦ MME.DWZSourceAligned.coarseAddress
            (outer (js i)) i r) ≠ 0) →
      ∃ j : Fin k, js = fun _ ↦ j) :
    MME.TensorObj.Restrict
      (MME.TensorObj.bigAdd (fun j ↦
        MME.DWZSourceAligned.brokenAddressObj K m
          (outer j) (copy j)))
      ((MME.TensorObj.kron (MME.CWObj K 6) (MME.CWObj K 6)).kronPow N) := by
  have hCoarse : MME.TensorObj.Restrict
      (MME.TensorObj.bigAdd (fun j ↦
        MME.DWZSourceAligned.coarseAddressObj K (outer j)))
      ((MME.TensorObj.kron (MME.CWObj K 6) (MME.CWObj K 6)).kronPow N) := by
    exact mme_induced_graded_address_blocks_restrict
      (MME.cwSquareCanonicalGrading K 6)
      (fun j ↦ MME.DWZSourceAligned.coarseAddress (outer j)) hInduced
  have hBroken : MME.TensorObj.Restrict
      (MME.TensorObj.bigAdd (fun j ↦
        MME.DWZSourceAligned.brokenAddressObj K m
          (outer j) (copy j)))
      (MME.TensorObj.bigAdd (fun j ↦
        MME.DWZSourceAligned.coarseAddressObj K (outer j))) := by
    apply mme_bigAdd_mono_restrict
    intro j
    exact (mme_dwz_source_aligned_broken_address_projection_certificate
      K m (outer j) (copy j)).1
  exact MME.TensorObj.Restrict.trans hBroken hCoarse
