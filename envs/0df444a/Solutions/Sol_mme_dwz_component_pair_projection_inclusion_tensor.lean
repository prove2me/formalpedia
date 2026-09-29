-- Prove2me | solution 1 for mme_dwz_component_pair_projection_inclusion_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:49:54.195993+00:00
-- url     : https://prove2.me/submissions/c22634d4-15e9-467f-9d24-4c33659b7570

import Definitions.Def_mme_dwz_component_pair_projection_data
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor
import Definitions.Def_mme_TypeGrading_kron

open MME Module TensorProduct PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ) :
    PiTensorProduct.map (componentPairInclusion K s m)
        (componentPairRestricted K s m).t =
      PiTensorProduct.map (componentPairProject K s m)
        (componentPairAmbient K s m).t := by
  let full := (canonicalComponentBlock K s).kronPow
    (DWZTable2Counts.component s * m)
  let restricted := restrictedComponentPower K s m
  have hleft :
      PiTensorProduct.map (componentPowerInclusion K s m) restricted.t =
        PiTensorProduct.map (componentPowerProject K s m) full.t := by
    classical
    exact (mme_basisZAllowed_blockSubtensor_inclusion_tensor
        full (componentPowerZBasis K s m) (componentWordAllowed s m))
  have hright :
      PiTensorProduct.map
          (fun i ↦ componentPowerInclusion K s m
            (swapFirstTwoPerm.symm i))
          (TensorObj.permObj swapFirstTwoPerm restricted).t =
        PiTensorProduct.map
          (fun i ↦ componentPowerProject K s m
            (swapFirstTwoPerm.symm i))
          (TensorObj.permObj swapFirstTwoPerm full).t := by
    change
      PiTensorProduct.map
          (fun i ↦ componentPowerInclusion K s m
            (swapFirstTwoPerm.symm i))
          ((PiTensorProduct.reindex K restricted.V swapFirstTwoPerm)
            restricted.t) =
        PiTensorProduct.map
          (fun i ↦ componentPowerProject K s m
            (swapFirstTwoPerm.symm i))
          ((PiTensorProduct.reindex K full.V swapFirstTwoPerm) full.t)
    rw [PiTensorProduct.map_reindex, PiTensorProduct.map_reindex, hleft]
  change
    PiTensorProduct.map (componentPairInclusion K s m)
        (interchange restricted.t
          (TensorObj.permObj swapFirstTwoPerm restricted).t) =
      PiTensorProduct.map (componentPairProject K s m)
        (interchange full.t
          (TensorObj.permObj swapFirstTwoPerm full).t)
  rw [show componentPairInclusion K s m =
      (fun i ↦ TensorProduct.map
        (componentPowerInclusion K s m i)
        (componentPowerInclusion K s m (swapFirstTwoPerm.symm i))) by
      rfl]
  rw [show componentPairProject K s m =
      (fun i ↦ TensorProduct.map
        (componentPowerProject K s m i)
        (componentPowerProject K s m (swapFirstTwoPerm.symm i))) by
      rfl]
  calc
    _ = interchange
        (PiTensorProduct.map (componentPowerInclusion K s m) restricted.t)
        (PiTensorProduct.map
          (fun i ↦ componentPowerInclusion K s m
            (swapFirstTwoPerm.symm i))
          (TensorObj.permObj swapFirstTwoPerm restricted).t) :=
      TensorObj.TypeGrading.kronMap_interchange
        (componentPowerInclusion K s m)
        (fun i ↦ componentPowerInclusion K s m
          (swapFirstTwoPerm.symm i))
        restricted.t (TensorObj.permObj swapFirstTwoPerm restricted).t
    _ = interchange
        (PiTensorProduct.map (componentPowerProject K s m) full.t)
        (PiTensorProduct.map
          (fun i ↦ componentPowerProject K s m
            (swapFirstTwoPerm.symm i))
          (TensorObj.permObj swapFirstTwoPerm full).t) := by
      rw [hleft, hright]
    _ = _ :=
      (TensorObj.TypeGrading.kronMap_interchange
        (componentPowerProject K s m)
        (fun i ↦ componentPowerProject K s m
          (swapFirstTwoPerm.symm i))
        full.t (TensorObj.permObj swapFirstTwoPerm full).t).symm
