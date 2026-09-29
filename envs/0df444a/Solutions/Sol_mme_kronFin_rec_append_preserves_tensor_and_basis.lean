-- Prove2me | solution 1 for mme_kronFin_rec_append_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T06:28:10.670185+00:00
-- url     : https://prove2.me/submissions/cd69db9f-f0f9-4943-a0de-40002180979a

import Definitions.Def_mme_kronFin_rec_append_data
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_kronFin_mode_pi_basis
import Mathlib.GroupTheory.Perm.Sign

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.TensorObj

/-- `interchange` evaluated on two pure tensors. -/
theorem mme_interchange_tprod
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- The modewise tensor commutor exchanges the two inputs of `interchange`. -/
theorem mme_interchange_comm
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W) :
    PiTensorProduct.map
        (fun i => (TensorProduct.comm K (W i) (V i)).toLinearMap)
        (interchange b a) =
      interchange a b := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      rw [mme_interchange_tprod, PiTensorProduct.map_tprod,
        mme_interchange_tprod, mul_comm c c']
      congr 2
    | add x y ih1 ih2 =>
      simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [LinearMap.add_apply, map_add, ih1, ih2]

/-- The modewise tensor associator reassociates three inputs of
`interchange`. -/
theorem mme_interchange_assoc
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W U : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W)
    (c : PiTensorProduct K U) :
    PiTensorProduct.map
        (fun i =>
          (TensorProduct.assoc K (V i) (W i) (U i)).toLinearMap)
        (interchange (interchange a b) c) =
      interchange a (interchange b c) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod ca v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod cb w =>
      induction c using PiTensorProduct.induction_on with
      | smul_tprod cc x =>
        simp only [map_smul, LinearMap.smul_apply, smul_smul]
        rw [mme_interchange_tprod, mme_interchange_tprod,
          PiTensorProduct.map_tprod, mme_interchange_tprod,
          mme_interchange_tprod,
          show cc * (cb * ca) = cc * cb * ca by ring]
        congr 1
      | add x y ih1 ih2 => simp only [map_add, ih1, ih2]
    | add x y ih1 ih2 =>
      simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [LinearMap.add_apply, map_add, ih1, ih2]

/-- The inverse modewise associator turns a right-associated interchange into
a left-associated one. -/
theorem mme_interchange_assoc_symm
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W U : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W)
    (c : PiTensorProduct K U) :
    PiTensorProduct.map
        (fun i =>
          (TensorProduct.assoc K (V i) (W i) (U i)).symm.toLinearMap)
        (interchange a (interchange b c)) =
      interchange (interchange a b) c := by
  rw [← mme_interchange_assoc a b c]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hcomp :
      (fun i =>
          (TensorProduct.assoc K (V i) (W i) (U i)).symm.toLinearMap ∘ₗ
            (TensorProduct.assoc K (V i) (W i) (U i)).toLinearMap) =
        (fun _ => LinearMap.id) := by
    funext i
    ext z
    simp
  rw [hcomp, PiTensorProduct.map_id]
  rfl

/-- The recursive product basis evaluates as the head basis vector tensored
with the product basis of the tail. -/
theorem kronFinModePiBasis_succ_apply
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

private theorem recAppendLength_succ_pos (m n : ℕ) :
    0 < recAppendLength (Nat.succ m) n := by
  simp only [recAppendLength, Nat.zero_lt_succ]

private theorem map_lid_symm_eq_interchange_one_rec
    {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (b : PiTensorProduct K V) :
    PiTensorProduct.map
        (fun i ↦ (TensorProduct.lid K (V i)).symm.toLinearMap) b =
      interchange (TensorObj.oneObj (K := K) (d := d)).t b := by
  induction b using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul]
      rw [PiTensorProduct.map_tprod]
      change c • tprod K
          (fun i ↦ (TensorProduct.lid K (V i)).symm (v i)) =
        c • interchange (tprod K (fun _ : Fin d ↦ (1 : K)))
          (tprod K v)
      rw [mme_interchange_tprod]
      congr 2
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy]
      rfl

/-- The recursion-aligned concatenation reassociator preserves the literal
tensor. -/
theorem kronFinRecAppendModeEquiv_preserves_tensor
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (m n : ℕ) (A : Fin m → TensorObj K d)
      (B : Fin n → TensorObj K d),
      PiTensorProduct.map
          (fun i ↦ (kronFinRecAppendModeEquiv m n A B i).toLinearMap)
          (TensorObj.kronFin (recAppendLength m n)
            (recAppendFamily m n A B)).t =
        (TensorObj.kron (TensorObj.kronFin m A)
          (TensorObj.kronFin n B)).t
  | 0, n, A, B => by
      exact map_lid_symm_eq_interchange_one_rec
        (K := K) (d := d) (TensorObj.kronFin n B).t
  | Nat.succ m, n, A, B => by
      let Atail : Fin m → TensorObj K d := fun r ↦ A r.succ
      let R := TensorObj.kronFin m Atail
      let S := TensorObj.kronFin n B
      have ih := kronFinRecAppendModeEquiv_preserves_tensor m n Atail B
      have hF :
          (fun i ↦
            (kronFinRecAppendModeEquiv (Nat.succ m) n A B i).toLinearMap) =
          fun i ↦
            (TensorProduct.assoc K ((A 0).V i) (R.V i) (S.V i)).symm.toLinearMap ∘ₗ
              TensorProduct.map
                (LinearMap.id : (A 0).V i →ₗ[K] (A 0).V i)
                (kronFinRecAppendModeEquiv m n Atail B i).toLinearMap := by
        funext i
        rfl
      change PiTensorProduct.map
          (fun i ↦
            (kronFinRecAppendModeEquiv (Nat.succ m) n A B i).toLinearMap)
          (interchange (A 0).t
            (TensorObj.kronFin (recAppendLength m n)
              (recAppendFamily m n Atail B)).t) =
        interchange (interchange (A 0).t R.t) S.t
      rw [hF]
      let inner : ∀ i,
          ((A 0).V i ⊗[K]
            (TensorObj.kronFin (recAppendLength m n)
              (recAppendFamily m n Atail B)).V i) →ₗ[K]
            ((A 0).V i ⊗[K] (R.V i ⊗[K] S.V i)) := fun i ↦
        TensorProduct.map
          (LinearMap.id : (A 0).V i →ₗ[K] (A 0).V i)
          (kronFinRecAppendModeEquiv m n Atail B i).toLinearMap
      let outerMap : ∀ i,
          ((A 0).V i ⊗[K] (R.V i ⊗[K] S.V i)) →ₗ[K]
            (((A 0).V i ⊗[K] R.V i) ⊗[K] S.V i) := fun i ↦
        (TensorProduct.assoc K ((A 0).V i) (R.V i) (S.V i)).symm.toLinearMap
      change PiTensorProduct.map (fun i ↦ outerMap i ∘ₗ inner i) _ = _
      have hcomp :
          PiTensorProduct.map (fun i ↦ outerMap i ∘ₗ inner i) =
            PiTensorProduct.map outerMap ∘ₗ PiTensorProduct.map inner :=
        PiTensorProduct.map_comp (g := outerMap) (f := inner)
      have happ :
          PiTensorProduct.map (fun i ↦ outerMap i ∘ₗ inner i)
              (interchange (A 0).t
                (TensorObj.kronFin (recAppendLength m n)
                  (recAppendFamily m n Atail B)).t) =
            PiTensorProduct.map outerMap
              (PiTensorProduct.map inner
                (interchange (A 0).t
                  (TensorObj.kronFin (recAppendLength m n)
                    (recAppendFamily m n Atail B)).t)) :=
        congrFun (congrArg DFunLike.coe hcomp) _
      refine happ.trans ?_
      dsimp only [inner]
      have hinner := TensorObj.TypeGrading.kronMap_interchange
        (fun _ : Fin d ↦ LinearMap.id)
        (fun i ↦
          (kronFinRecAppendModeEquiv m n Atail B i).toLinearMap)
        (A 0).t
        (TensorObj.kronFin (recAppendLength m n)
          (recAppendFamily m n Atail B)).t
      calc
        PiTensorProduct.map outerMap
            (PiTensorProduct.map inner
              (interchange (A 0).t
                (TensorObj.kronFin (recAppendLength m n)
                  (recAppendFamily m n Atail B)).t)) =
            PiTensorProduct.map outerMap
              (interchange
                (PiTensorProduct.map (fun _ : Fin d ↦ LinearMap.id) (A 0).t)
                (PiTensorProduct.map
                  (fun i ↦
                    (kronFinRecAppendModeEquiv m n Atail B i).toLinearMap)
                  (TensorObj.kronFin (recAppendLength m n)
                    (recAppendFamily m n Atail B)).t)) := by
              exact congrArg (fun z ↦ PiTensorProduct.map outerMap z) hinner
        _ = PiTensorProduct.map outerMap
              (interchange (A 0).t (interchange R.t S.t)) := by
              rw [PiTensorProduct.map_id, LinearMap.id_apply, ih]
              change PiTensorProduct.map outerMap
                  (interchange (A 0).t (interchange R.t S.t)) = _
              rfl
        _ = interchange (interchange (A 0).t R.t) S.t := by
              dsimp only [outerMap]
              exact mme_interchange_assoc_symm (A 0).t R.t S.t

/-- The left word obtained by splitting a word for `recAppendFamily`. -/
theorem kronFinRecAppendModeEquiv_basis
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (m n : ℕ) (A : Fin m → TensorObj K d)
      (B : Fin n → TensorObj K d) (i : Fin d)
      (indexA : Fin m → Type u) (indexB : Fin n → Type u)
      (bA : ∀ r, Basis (indexA r) K ((A r).V i))
      (bB : ∀ r, Basis (indexB r) K ((B r).V i))
      (w : ∀ r, recAppendFamily m n indexA indexB r),
      kronFinRecAppendModeEquiv m n A B i
          (TensorObj.kronFinModePiBasis (recAppendLength m n)
            (recAppendFamily m n A B) i
            (recAppendBasisFamily m n A B i indexA indexB bA bB) w) =
        (TensorObj.kronFinModePiBasis m A i bA
          (recAppendLeftWord w)) ⊗ₜ[K]
        (TensorObj.kronFinModePiBasis n B i bB
          (recAppendRightWord w))
  | 0, n, A, B, i, indexA, indexB, bA, bB, w => by
      simp only [recAppendLength, recAppendFamily,
        recAppendBasisFamily, recAppendLeftWord, recAppendRightWord,
        kronFinRecAppendModeEquiv]
      change (TensorProduct.lid K ((TensorObj.kronFin n B).V i)).symm
          (TensorObj.kronFinModePiBasis n B i bB w) =
        (Module.Basis.singleton ((j : Fin 0) → indexA j) K
          (fun r ↦ r.elim0)) ⊗ₜ[K]
            TensorObj.kronFinModePiBasis n B i bB w
      rw [Module.Basis.singleton_apply]
      exact TensorProduct.lid_symm_apply _
  | Nat.succ m, n, A, B, i, indexA, indexB, bA, bB, w => by
      let Atail : Fin m → TensorObj K d := fun r ↦ A r.succ
      let indexTail : Fin m → Type u := fun r ↦ indexA r.succ
      let wHead : indexA 0 :=
        w ⟨0, recAppendLength_succ_pos m n⟩
      let bTail : ∀ r, Basis (indexTail r) K ((Atail r).V i) :=
        fun r ↦ bA r.succ
      let wTail : ∀ r,
          recAppendFamily m n indexTail indexB r := fun r ↦ w r.succ
      have ih := kronFinRecAppendModeEquiv_basis m n Atail B i
        indexTail indexB bTail bB wTail
      have hsource :
          TensorObj.kronFinModePiBasis
              (recAppendLength (Nat.succ m) n)
              (recAppendFamily (Nat.succ m) n A B) i
              (recAppendBasisFamily (Nat.succ m) n A B i
                indexA indexB bA bB) w =
            (bA 0 wHead) ⊗ₜ[K]
              TensorObj.kronFinModePiBasis (recAppendLength m n)
                (recAppendFamily m n Atail B) i
                (recAppendBasisFamily m n Atail B i
                  indexTail indexB bTail bB) wTail := by
        exact kronFinModePiBasis_succ_apply
            (recAppendFamily (Nat.succ m) n A B) i
            (recAppendBasisFamily (Nat.succ m) n A B i
              indexA indexB bA bB) w
      rw [hsource]
      change (TensorProduct.assoc K ((A 0).V i)
          ((TensorObj.kronFin m Atail).V i)
          ((TensorObj.kronFin n B).V i)).symm
          ((TensorProduct.congr (LinearEquiv.refl K ((A 0).V i))
            (kronFinRecAppendModeEquiv m n Atail B i))
            ((bA 0 wHead) ⊗ₜ[K]
              TensorObj.kronFinModePiBasis (recAppendLength m n)
                (recAppendFamily m n Atail B) i
                (recAppendBasisFamily m n Atail B i
                  indexTail indexB bTail bB) wTail)) = _
      rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, ih]
      have hleft :
          recAppendLeftWord
              (m := Nat.succ m) (n := n)
              (indexA := indexA) (indexB := indexB) w =
          Fin.cons wHead
            (recAppendLeftWord
              (m := m) (n := n)
              (indexA := indexTail) (indexB := indexB) wTail) := by
        rfl
      have hright :
          recAppendRightWord
              (m := Nat.succ m) (n := n)
              (indexA := indexA) (indexB := indexB) w =
            recAppendRightWord
              (m := m) (n := n)
              (indexA := indexTail) (indexB := indexB) wTail := by
        rfl
      rw [hleft, hright, kronFinModePiBasis_succ_apply]
      exact TensorProduct.assoc_symm_tmul _ _ _


end MME.TensorObj

theorem solution
    {K : Type u} [Field K] {d : ℕ}
    (m n : ℕ) (A : Fin m → TensorObj K d)
    (B : Fin n → TensorObj K d) :
    PiTensorProduct.map
        (fun i ↦
          (MME.TensorObj.kronFinRecAppendModeEquiv m n A B i).toLinearMap)
        (TensorObj.kronFin (MME.TensorObj.recAppendLength m n)
          (MME.TensorObj.recAppendFamily m n A B)).t =
      (TensorObj.kron (TensorObj.kronFin m A)
        (TensorObj.kronFin n B)).t ∧
    ∀ (i : Fin d) (indexA : Fin m → Type u)
      (indexB : Fin n → Type u)
      (bA : ∀ r, Basis (indexA r) K ((A r).V i))
      (bB : ∀ r, Basis (indexB r) K ((B r).V i))
      (w : ∀ r,
        MME.TensorObj.recAppendFamily m n indexA indexB r),
      MME.TensorObj.kronFinRecAppendModeEquiv m n A B i
          (TensorObj.kronFinModePiBasis
            (MME.TensorObj.recAppendLength m n)
            (MME.TensorObj.recAppendFamily m n A B) i
            (MME.TensorObj.recAppendBasisFamily m n A B i
              indexA indexB bA bB) w) =
        (TensorObj.kronFinModePiBasis m A i bA
          (MME.TensorObj.recAppendLeftWord w)) ⊗ₜ[K]
        (TensorObj.kronFinModePiBasis n B i bB
          (MME.TensorObj.recAppendRightWord w)) := by
  exact ⟨MME.TensorObj.kronFinRecAppendModeEquiv_preserves_tensor m n A B,
    fun i indexA indexB bA bB w ↦
      MME.TensorObj.kronFinRecAppendModeEquiv_basis m n A B i
        indexA indexB bA bB w⟩
