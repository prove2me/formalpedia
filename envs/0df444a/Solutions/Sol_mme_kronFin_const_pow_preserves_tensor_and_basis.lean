-- Prove2me | solution 1 for mme_kronFin_const_pow_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:40:08.654121+00:00
-- url     : https://prove2.me/submissions/5ea0b931-473e-4edb-bc16-9495ec3a51ea

import Definitions.Def_mme_kronFin_const_pow_mode_equiv
import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_TypeGrading_kron

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

private theorem preserves
    {K : Type u} [Field K] (T : TensorObj K 3) :
    ∀ n : ℕ,
      PiTensorProduct.map
          (fun i ↦ (MME.TensorObj.kronFinConstPowModeEquiv T i n).toLinearMap)
          (TensorObj.kronFin n (fun _ ↦ T)).t =
        (T.kronPow n).t
  | 0 => by
      change PiTensorProduct.map (fun _ : Fin 3 ↦ LinearMap.id)
        (TensorObj.oneObj (K := K) (d := 3)).t = _
      rw [PiTensorProduct.map_id]
      rfl
  | n + 1 => by
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map
            (LinearMap.id : T.V i →ₗ[K] T.V i)
            (MME.TensorObj.kronFinConstPowModeEquiv T i n).toLinearMap)
          (interchange T.t
            (TensorObj.kronFin n (fun _ ↦ T)).t) =
        interchange T.t (T.kronPow n).t
      rw [TensorObj.TypeGrading.kronMap_interchange,
        PiTensorProduct.map_id, preserves T n]
      rfl

private theorem piBasis_succ
    {K : Type u} [Field K] {n : ℕ}
    (T : TensorObj K 3) (i : Fin 3) {index : Type u}
    (b : Basis index K (T.V i)) (w : Fin (n + 1) → index) :
    TensorObj.kronFinModePiBasis (n + 1) (fun _ ↦ T) i
        (fun _ ↦ b) w =
      b (w 0) ⊗ₜ[K]
        TensorObj.kronFinModePiBasis n (fun _ ↦ T) i
          (fun _ ↦ b) (fun r ↦ w r.succ) := by
  change (((b.tensorProduct
    (TensorObj.kronFinModePiBasis n (fun _ ↦ T) i
      (fun _ ↦ b))).reindex
        (Fin.consEquiv (fun _ : Fin (n + 1) ↦ index))) w) = _
  rw [Module.Basis.reindex_apply, Fin.consEquiv_symm_apply,
    Module.Basis.tensorProduct_apply]
  rfl

private theorem basis
    {K : Type u} [Field K] (T : TensorObj K 3) (i : Fin 3)
    {index : Type u} (b : Basis index K (T.V i)) :
    ∀ (n : ℕ) (w : Fin n → index),
      MME.TensorObj.kronFinConstPowModeEquiv T i n
          (TensorObj.kronFinModePiBasis n (fun _ ↦ T) i
            (fun _ ↦ b) w) =
        MME.DWZComponentRestriction.kronPowModeBasis T i b n
          (MME.DWZComponentRestriction.PowIndex.ofFun n w)
  | 0, w => by
      change (LinearEquiv.refl K K)
          (Basis.singleton (∀ _ : Fin 0, index) K w) =
        Basis.singleton PUnit K PUnit.unit
      rw [Module.Basis.singleton_apply, Module.Basis.singleton_apply]
      rfl
  | n + 1, w => by
      rw [piBasis_succ]
      change TensorProduct.congr (LinearEquiv.refl K (T.V i))
          (MME.TensorObj.kronFinConstPowModeEquiv T i n)
          (b (w 0) ⊗ₜ[K]
            TensorObj.kronFinModePiBasis n (fun _ ↦ T) i
              (fun _ ↦ b) (fun r ↦ w r.succ)) = _
      rw [TensorProduct.congr_tmul]
      change b (w 0) ⊗ₜ[K]
          MME.TensorObj.kronFinConstPowModeEquiv T i n
            (TensorObj.kronFinModePiBasis n (fun _ ↦ T) i
              (fun _ ↦ b) (fun r ↦ w r.succ)) = _
      rw [basis]
      change b (w 0) ⊗ₜ[K]
          MME.DWZComponentRestriction.kronPowModeBasis T i b n
            (MME.DWZComponentRestriction.PowIndex.ofFun n
              (fun r ↦ w r.succ)) =
        (b.tensorProduct
          (MME.DWZComponentRestriction.kronPowModeBasis T i b n))
          (w 0, MME.DWZComponentRestriction.PowIndex.ofFun n
            (fun r ↦ w r.succ))
      rw [Module.Basis.tensorProduct_apply]

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) (n : ℕ) :
    PiTensorProduct.map
        (fun i ↦ (MME.TensorObj.kronFinConstPowModeEquiv T i n).toLinearMap)
        (TensorObj.kronFin n (fun _ ↦ T)).t =
      (T.kronPow n).t ∧
    ∀ (i : Fin 3) {index : Type u} (b : Basis index K (T.V i))
      (w : Fin n → index),
      MME.TensorObj.kronFinConstPowModeEquiv T i n
          (TensorObj.kronFinModePiBasis n (fun _ ↦ T) i
            (fun _ ↦ b) w) =
        MME.DWZComponentRestriction.kronPowModeBasis T i b n
          (MME.DWZComponentRestriction.PowIndex.ofFun n w) := by
  exact ⟨preserves T n, fun i _ b w ↦ basis T i b n w⟩
