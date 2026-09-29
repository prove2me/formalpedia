-- Prove2me | solution 1 for mme_cyclicSymmetrization_mono_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:47:18.100587+00:00
-- url     : https://prove2.me/submissions/1f233fc0-385d-4b1f-901d-96a7c1b616d5

import Definitions.Def_mme_CW_coupled_value

open MME PiTensorProduct TensorProduct

universe u


namespace CWCyclicSymmetrizationRestrict

theorem interchange_tprod
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    MME.interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (MME.interchange (tprod K v)) (tprod K w) = _
  unfold MME.interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (MME.interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem map_interchange
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V₁ V₂ V₃ V₄ : ι → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
        (MME.interchange t₁ t₂) =
      MME.interchange (PiTensorProduct.map f t₁)
        (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c' v' =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        interchange_tprod]
      simp only [TensorProduct.map_tmul]
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  | add x y ihx ihy => simp only [map_add, LinearMap.add_apply, ihx, ihy]

theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ}
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X') (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  refine ⟨fun i => TensorProduct.map (f i) (g i), ?_⟩
  show PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
      (MME.interchange X'.t Y'.t) = MME.interchange X.t Y.t
  rw [map_interchange, hf, hg]

theorem permute_restrict
    {K : Type u} [Field K]
    (e : Equiv.Perm (Fin 3)) {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (permuteModes e X) (permuteModes e Y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun i => f (e.symm i), ?_⟩
  show PiTensorProduct.map (fun i => f (e.symm i))
      ((PiTensorProduct.reindex K Y.V e) Y.t) =
    (PiTensorProduct.reindex K X.V e) X.t
  rw [PiTensorProduct.map_reindex, hf]

end CWCyclicSymmetrizationRestrict

theorem solution
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (cyclicSymmetrization X) (cyclicSymmetrization Y) := by
  unfold cyclicSymmetrization
  exact CWCyclicSymmetrizationRestrict.kron_restrict h
    (CWCyclicSymmetrizationRestrict.kron_restrict
      (CWCyclicSymmetrizationRestrict.permute_restrict _ h)
      (CWCyclicSymmetrizationRestrict.permute_restrict _ h))
