-- Prove2me | solution 1 for mme_kronPow_modewise_maps_preserve_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:33:23.693464+00:00
-- url     : https://prove2.me/submissions/073f6af8-5a2c-4135-ae36-4250b2150631

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj PiTensorProduct

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    (f : ∀ i : Fin d, T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t) : ∀ n : ℕ,
    PiTensorProduct.map (fun i ↦ kronPowModeMap i (f i) n)
        (T.kronPow n).t = (S.kronPow n).t
  | 0 => by
      change PiTensorProduct.map (fun _ ↦ LinearMap.id)
          (TensorObj.oneObj (K := K) (d := d)).t =
        (TensorObj.oneObj (K := K) (d := d)).t
      rw [PiTensorProduct.map_id]
      rfl
  | n + 1 => by
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map (f i)
            (kronPowModeMap i (f i) n))
          (interchange T.t (T.kronPow n).t) =
        interchange S.t (S.kronPow n).t
      rw [TensorObj.TypeGrading.kronMap_interchange, hf]
      rw [solution f hf n]
