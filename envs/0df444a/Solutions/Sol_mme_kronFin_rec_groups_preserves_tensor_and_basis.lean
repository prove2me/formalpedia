-- Prove2me | solution 1 for mme_kronFin_rec_groups_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:02:06.081158+00:00
-- url     : https://prove2.me/submissions/96685a98-d446-4804-a26d-3a4c8474782d

import Definitions.Def_mme_kronFin_rec_groups_data
import Theorems.Thm_mme_kronFin_rec_append_preserves_tensor_and_basis
import Definitions.Def_mme_TypeGrading_kron

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.TensorObj

private theorem kronFinModePiBasis_succ_apply_groups
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 1) → TensorObj K d) (i : Fin d)
    {index : Fin (n + 1) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (w : ∀ r, index r) :
    TensorObj.kronFinModePiBasis (n + 1) T i b w =
      (b 0 (w 0)) ⊗ₜ[K]
        (TensorObj.kronFinModePiBasis n
          (fun r : Fin n ↦ T r.succ) i
          (fun r ↦ b r.succ) (fun r ↦ w r.succ)) := by
  change (((b 0).tensorProduct
    (TensorObj.kronFinModePiBasis n
      (fun r : Fin n ↦ T r.succ) i
      (fun r ↦ b r.succ))).reindex (Fin.consEquiv index)) w = _
  rw [Module.Basis.reindex_apply, Fin.consEquiv_symm_apply,
    Module.Basis.tensorProduct_apply]
  rfl

private theorem recGroups_preserves_tensor
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (k : ℕ) (count : Fin k → ℕ)
      (X : Fin k → TensorObj K d),
      PiTensorProduct.map
          (fun i ↦
            (kronFinRecGroupsModeEquiv k count X i).toLinearMap)
          (TensorObj.kronFin (recGroupLength k count)
            (recGroupFamily k count X)).t =
        (TensorObj.kronFin k (fun s ↦
          TensorObj.kronFin (count s) (fun _ ↦ X s))).t
  | 0, count, X => by
      change PiTensorProduct.map (fun _ : Fin d ↦ LinearMap.id)
        (TensorObj.oneObj (K := K) (d := d)).t = _
      rw [PiTensorProduct.map_id]
      rfl
  | k + 1, count, X => by
      let tailCount : Fin k → ℕ := fun s ↦ count s.succ
      let tailX : Fin k → TensorObj K d := fun s ↦ X s.succ
      let first : Fin (count 0) → TensorObj K d := fun _ ↦ X 0
      let flatTail := recGroupFamily k tailCount tailX
      let A := TensorObj.kronFin (count 0) first
      let B := TensorObj.kronFin (recGroupLength k tailCount) flatTail
      have happend :=
        (mme_kronFin_rec_append_preserves_tensor_and_basis
          (count 0) (recGroupLength k tailCount) first flatTail).1
      have htail := recGroups_preserves_tensor k tailCount tailX
      have hF :
          (fun i ↦
            (kronFinRecGroupsModeEquiv (k + 1) count X i).toLinearMap) =
          fun i ↦
            (TensorProduct.map
              (LinearMap.id : A.V i →ₗ[K] A.V i)
              (kronFinRecGroupsModeEquiv k tailCount tailX i).toLinearMap) ∘ₗ
            (kronFinRecAppendModeEquiv
              (count 0) (recGroupLength k tailCount)
              first flatTail i).toLinearMap := by
        funext i
        rfl
      rw [hF]
      have happend' :
          PiTensorProduct.map
              (fun i ↦ (kronFinRecAppendModeEquiv
                (count 0) (recGroupLength k tailCount)
                first flatTail i).toLinearMap)
              (TensorObj.kronFin (recGroupLength (k + 1) count)
                (recGroupFamily (k + 1) count X)).t =
            (TensorObj.kron A B).t := by
        simpa only [recGroupLength, recGroupFamily] using happend
      have hkron := TensorObj.TypeGrading.kronMap_interchange
        (fun _ : Fin d ↦ LinearMap.id)
        (fun i ↦
          (kronFinRecGroupsModeEquiv k tailCount tailX i).toLinearMap)
        A.t B.t
      have h1 :
          PiTensorProduct.map
              (fun i ↦
                TensorProduct.map
                    (LinearMap.id : A.V i →ₗ[K] A.V i)
                    (kronFinRecGroupsModeEquiv k tailCount tailX i).toLinearMap ∘ₗ
                  (kronFinRecAppendModeEquiv
                    (count 0) (recGroupLength k tailCount)
                    first flatTail i).toLinearMap)
              (TensorObj.kronFin (recGroupLength (k + 1) count)
                (recGroupFamily (k + 1) count X)).t =
            PiTensorProduct.map
              (fun i ↦ TensorProduct.map
                (LinearMap.id : A.V i →ₗ[K] A.V i)
                (kronFinRecGroupsModeEquiv k tailCount tailX i).toLinearMap)
              (PiTensorProduct.map
                (fun i ↦ (kronFinRecAppendModeEquiv
                  (count 0) (recGroupLength k tailCount)
                  first flatTail i).toLinearMap)
                (TensorObj.kronFin (recGroupLength (k + 1) count)
                  (recGroupFamily (k + 1) count X)).t) :=
        congrFun (congrArg DFunLike.coe
          (PiTensorProduct.map_comp
            (fun i ↦ TensorProduct.map
              (LinearMap.id : A.V i →ₗ[K] A.V i)
              (kronFinRecGroupsModeEquiv k tailCount tailX i).toLinearMap)
            (fun i ↦ (kronFinRecAppendModeEquiv
              (count 0) (recGroupLength k tailCount)
              first flatTail i).toLinearMap))) _
      have h2 := congrArg
        (fun z ↦ PiTensorProduct.map
          (fun i ↦ TensorProduct.map
            (LinearMap.id : A.V i →ₗ[K] A.V i)
            (kronFinRecGroupsModeEquiv k tailCount tailX i).toLinearMap) z)
        happend'
      have h3 :
          PiTensorProduct.map
              (fun i ↦ TensorProduct.map
                (LinearMap.id : A.V i →ₗ[K] A.V i)
                (kronFinRecGroupsModeEquiv k tailCount tailX i).toLinearMap)
              (TensorObj.kron A B).t =
            (TensorObj.kronFin (k + 1) (fun s ↦
              TensorObj.kronFin (count s) (fun _ ↦ X s))).t := by
        change PiTensorProduct.map
            (fun i ↦ TensorProduct.map
              (LinearMap.id : A.V i →ₗ[K] A.V i)
              (kronFinRecGroupsModeEquiv k tailCount tailX i).toLinearMap)
            (interchange A.t B.t) = _
        rw [hkron, PiTensorProduct.map_id, htail]
        rfl
      exact h1.trans (h2.trans h3)

private theorem recGroups_basis
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (k : ℕ) (count : Fin k → ℕ)
      (X : Fin k → TensorObj K d) (i : Fin d)
      (index : Fin k → Type u)
      (b : ∀ s, Basis (index s) K ((X s).V i))
      (w : ∀ r, recGroupFamily k count index r),
      kronFinRecGroupsModeEquiv k count X i
          (TensorObj.kronFinModePiBasis (recGroupLength k count)
            (recGroupFamily k count X) i
            (recGroupBasisFamily k count X i index b) w) =
        TensorObj.kronFinModePiBasis k
          (fun s ↦ TensorObj.kronFin (count s) (fun _ ↦ X s)) i
          (fun s ↦ TensorObj.kronFinModePiBasis (count s)
            (fun _ ↦ X s) i (fun _ ↦ b s))
          (recGroupWord w)
  | 0, count, X, i, index, b, w => by
      let : Unique
          (∀ r : Fin (recGroupLength 0 count),
            recGroupFamily 0 count index r) :=
        { default := fun r ↦ r.elim0
          uniq := fun _ ↦ by
            funext r
            exact r.elim0 }
      let : Unique (∀ s : Fin 0, Fin (count s) → index s) :=
        { default := fun s ↦ s.elim0
          uniq := fun _ ↦ by
            funext s
            exact s.elim0 }
      simp only [recGroupLength, recGroupFamily,
        kronFinRecGroupsModeEquiv, recGroupBasisFamily,
        recGroupWord, TensorObj.kronFinModePiBasis]
      calc
        _ = (1 : K) := by
          change (Basis.singleton _ K) w = 1
          exact Module.Basis.singleton_apply _ K w
        _ = _ := by
          symm
          change (Basis.singleton _ K) (fun s : Fin 0 ↦ s.elim0) = 1
          exact Module.Basis.singleton_apply _ K _
  | k + 1, count, X, i, index, b, w => by
      let tailCount : Fin k → ℕ := fun s ↦ count s.succ
      let tailX : Fin k → TensorObj K d := fun s ↦ X s.succ
      let tailIndex : Fin k → Type u := fun s ↦ index s.succ
      let first : Fin (count 0) → TensorObj K d := fun _ ↦ X 0
      let firstIndex : Fin (count 0) → Type u := fun _ ↦ index 0
      let flatTail := recGroupFamily k tailCount tailX
      let flatTailIndex := recGroupFamily k tailCount tailIndex
      let wTail := recAppendRightWord w
      have happend :=
        (mme_kronFin_rec_append_preserves_tensor_and_basis
          (count 0) (recGroupLength k tailCount)
          first flatTail).2 i firstIndex flatTailIndex
          (fun _ ↦ b 0)
          (recGroupBasisFamily k tailCount tailX i tailIndex
            (fun s ↦ b s.succ)) w
      have htail := recGroups_basis
        k tailCount tailX i tailIndex (fun s ↦ b s.succ) wTail
      have happend' :
          kronFinRecAppendModeEquiv
              (count 0) (recGroupLength k tailCount)
              first flatTail i
              (TensorObj.kronFinModePiBasis
                (recGroupLength (k + 1) count)
                (recGroupFamily (k + 1) count X) i
                (recGroupBasisFamily (k + 1) count X i index b) w) =
            (TensorObj.kronFinModePiBasis (count 0) first i
                (fun _ ↦ b 0) (recAppendLeftWord w)) ⊗ₜ[K]
              (TensorObj.kronFinModePiBasis
                (recGroupLength k tailCount) flatTail i
                (recGroupBasisFamily k tailCount tailX i tailIndex
                  (fun s ↦ b s.succ))
                (recAppendRightWord w)) := by
        exact happend
      change (TensorProduct.congr (LinearEquiv.refl K _)
          (kronFinRecGroupsModeEquiv k tailCount tailX i))
        (kronFinRecAppendModeEquiv
          (count 0) (recGroupLength k tailCount)
          first flatTail i
          (TensorObj.kronFinModePiBasis (recGroupLength (k + 1) count)
            (recGroupFamily (k + 1) count X) i
            (recGroupBasisFamily (k + 1) count X i index b) w)) = _
      rw [happend', TensorProduct.congr_tmul, LinearEquiv.refl_apply, htail]
      rw [kronFinModePiBasis_succ_apply_groups]
      rfl

end MME.TensorObj

theorem solution
    {K : Type u} [Field K] {d : ℕ}
    (k : ℕ) (count : Fin k → ℕ)
    (X : Fin k → TensorObj K d) :
    PiTensorProduct.map
        (fun i ↦
          (MME.TensorObj.kronFinRecGroupsModeEquiv k count X i).toLinearMap)
        (TensorObj.kronFin (MME.TensorObj.recGroupLength k count)
          (MME.TensorObj.recGroupFamily k count X)).t =
      (TensorObj.kronFin k (fun s ↦
        TensorObj.kronFin (count s) (fun _ ↦ X s))).t ∧
    ∀ (i : Fin d) (index : Fin k → Type u)
      (b : ∀ s, Basis (index s) K ((X s).V i))
      (w : ∀ r,
        MME.TensorObj.recGroupFamily k count index r),
      MME.TensorObj.kronFinRecGroupsModeEquiv k count X i
          (TensorObj.kronFinModePiBasis
            (MME.TensorObj.recGroupLength k count)
            (MME.TensorObj.recGroupFamily k count X) i
            (MME.TensorObj.recGroupBasisFamily k count X i index b) w) =
        TensorObj.kronFinModePiBasis k
          (fun s ↦ TensorObj.kronFin (count s) (fun _ ↦ X s)) i
          (fun s ↦ TensorObj.kronFinModePiBasis (count s)
            (fun _ ↦ X s) i (fun _ ↦ b s))
          (MME.TensorObj.recGroupWord w) := by
  exact ⟨MME.TensorObj.recGroups_preserves_tensor k count X,
    fun i index b w ↦
      MME.TensorObj.recGroups_basis k count X i index b w⟩
