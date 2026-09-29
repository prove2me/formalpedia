-- Prove2me | solution 1 for mme_dwz_source_broken_family_to_grouped_standard_of_mixed_maps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:19:31.068064+00:00
-- url     : https://prove2.me/submissions/976e8288-414a-4989-90d1-a330ed4b3589

import Theorems.Thm_mme_dwz_source_broken_family_transport_to_grouped_standard
import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K]
    (S : TensorObj K 3) {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (houter : ∀ j : Fin k, ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer j r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K]
      (DWZSourceAligned.brokenAddressObj K m
        (outer j) (copy j)).V i)
    (hDiagonal : ∀ j : Fin k,
      PiTensorProduct.map (f j) S.t =
        (DWZSourceAligned.brokenAddressObj K m
          (outer j) (copy j)).t)
    (hMixedZero : ∀ js : Fin 3 → Fin k,
      (∀ j : Fin k, js ≠ fun _ ↦ j) →
      PiTensorProduct.map (fun i ↦ f (js i) i) S.t = 0) :
    ∃ standardCopy : Fin k → DWZSquare.BrokenBlockCopy
        (DWZComponentRestriction.DWZStandardBlock m),
      (∀ j : Fin k,
        (standardCopy j).nonholes.card = (copy j).nonholes.card) ∧
      let D : DWZComponentRestriction.DWZStandardLabelledData K m :=
        { X := TensorObj.kronFin 15
            (fun r : Fin 15 ↦
              DWZComponentRestriction.restrictedComponentPower K r m)
          basis := TensorObj.kronFinModePiBasis 15
            (fun r : Fin 15 ↦
              DWZComponentRestriction.restrictedComponentPower K r m) 2
            (fun r ↦
              DWZComponentRestriction.restrictedComponentZBasis K r m)
          label := DWZComponentRestriction.groupedUsefulBlock m }
      let G : Fin k → D.X.TypeGrading 2 := fun j ↦
        D.X.basisZAllowedGrading D.basis
          (fun W ↦ D.label W ∈ (standardCopy j).nonholes)
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦
          (G j).blockSubtensor (fun _ ↦ 0))) S := by
  have hSource : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        DWZSourceAligned.brokenAddressObj K m
          (outer j) (copy j))) S :=
    mme_tensor_family_direct_sum_restrict_of_mixed_maps
      S (fun j ↦ DWZSourceAligned.brokenAddressObj K m
        (outer j) (copy j)) f hDiagonal hMixedZero
  exact mme_dwz_source_broken_family_transport_to_grouped_standard
    S outer houter hm copy hSource
