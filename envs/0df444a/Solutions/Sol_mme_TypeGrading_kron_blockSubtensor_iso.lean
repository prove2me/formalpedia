-- Prove2me | solution 1 for mme_TypeGrading_kron_blockSubtensor_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:24:07.290336+00:00
-- url     : https://prove2.me/submissions/ce85c917-03ea-4801-8abb-f3541b935c16

import Definitions.Def_mme_TypeGrading_kron

open MME TensorProduct PiTensorProduct
open MME.TensorObj.TypeGrading

universe u

theorem solution
    {K : Type u} [Field K] {d tx ty : ℕ}
    {X Y : TensorObj K d}
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (sx : Fin d → Fin tx) (sy : Fin d → Fin ty) :
    TensorObj.Isomorphic
      (TensorObj.kron (GX.blockSubtensor sx) (GY.blockSubtensor sy))
      ((kronGrading GX GY).blockSubtensor
        (fun i ↦ finProdFinEquiv (sx i, sy i))) := by
  constructor
  · refine ⟨fun i ↦
      (classKronEquiv GX GY i (sx i) (sy i)).symm.toLinearMap, ?_⟩
    change
      PiTensorProduct.map
          (fun i ↦
            (classKronEquiv GX GY i (sx i) (sy i)).symm.toLinearMap)
          ((kronGrading GX GY).blockTensor
            (fun i ↦ finProdFinEquiv (sx i, sy i))) =
        interchange (GX.blockTensor sx) (GY.blockTensor sy)
    rw [kronGrading_blockTensor_eq]
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    have hinv :
        (fun i ↦
          (classKronEquiv GX GY i (sx i) (sy i)).symm.toLinearMap.comp
            (classKronLift GX GY i (sx i) (sy i))) =
        (fun _ ↦ LinearMap.id) := by
      funext i
      apply LinearMap.ext
      intro z
      exact (classKronEquiv GX GY i (sx i) (sy i)).symm_apply_apply z
    rw [hinv, PiTensorProduct.map_id]
    rfl
  · refine ⟨fun i ↦
      (classKronEquiv GX GY i (sx i) (sy i)).toLinearMap, ?_⟩
    change
      PiTensorProduct.map
          (fun i ↦
            (classKronEquiv GX GY i (sx i) (sy i)).toLinearMap)
          (interchange (GX.blockTensor sx) (GY.blockTensor sy)) =
        (kronGrading GX GY).blockTensor
          (fun i ↦ finProdFinEquiv (sx i, sy i))
    exact (kronGrading_blockTensor_eq GX GY sx sy).symm
