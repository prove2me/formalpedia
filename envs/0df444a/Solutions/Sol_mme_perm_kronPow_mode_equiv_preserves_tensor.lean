-- Prove2me | solution 1 for mme_perm_kronPow_mode_equiv_preserves_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:46:52.089987+00:00
-- url     : https://prove2.me/submissions/11fc80ed-00b2-42ec-87dd-6a98209bd966

import Definitions.Def_mme_perm_kronPow_mode_equiv

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem interchange_tprod_local
    {K : Type u} [Field K]
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem map_interchange_local
    {K : Type u} [Field K]
    {V₁ V₂ V₃ V₄ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (g i))
        (interchange t₁ t₂) =
      interchange (PiTensorProduct.map f t₁)
        (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      induction t₂ using PiTensorProduct.induction_on with
      | smul_tprod c' v' =>
          simp only [map_smul, LinearMap.smul_apply]
          rw [interchange_tprod_local, PiTensorProduct.map_tprod,
            PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
            interchange_tprod_local]
          simp only [TensorProduct.map_tmul]
      | add x y ih₁ ih₂ =>
          simp only [map_add, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

theorem solution
    {K : Type u} [Field K] (e : Equiv.Perm (Fin 3))
    (T : TensorObj K 3) (n : ℕ) :
    PiTensorProduct.map
        (fun i ↦ (MME.TensorObj.permKronPowModeEquiv e T i n).toLinearMap)
        ((TensorObj.permObj e T).kronPow n).t =
      (TensorObj.permObj e (T.kronPow n)).t := by
  induction n with
  | zero =>
      change PiTensorProduct.map (fun _ ↦ LinearMap.id)
          (tprod K (fun _ : Fin 3 ↦ (1 : K))) =
        PiTensorProduct.reindex K (fun _ : Fin 3 ↦ K) e
          (tprod K (fun _ : Fin 3 ↦ (1 : K)))
      rw [PiTensorProduct.map_id, PiTensorProduct.reindex_tprod]
      rfl
  | succ n ih =>
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map LinearMap.id
            (MME.TensorObj.permKronPowModeEquiv e T i n).toLinearMap)
          (interchange
            (PiTensorProduct.reindex K T.V e T.t)
            ((TensorObj.permObj e T).kronPow n).t) =
        PiTensorProduct.reindex K
          (fun i ↦ TensorProduct K (T.V i) ((T.kronPow n).V i)) e
          (interchange T.t (T.kronPow n).t)
      rw [map_interchange_local, ih, PiTensorProduct.map_id,
        reindex_interchange]
      rfl
