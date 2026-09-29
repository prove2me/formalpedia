-- Prove2me | solution 1 for mme_dwz_basis_label_owner_map_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:22:02.490845+00:00
-- url     : https://prove2.me/submissions/a3f3c9ba-ecf4-4bf9-9d42-0a811fe27366

import Definitions.Def_mme_dwz_basis_label_projection

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem basis_projection_basis
    {ι β V : Type*} {K : Type u} [Field K]
    [AddCommMonoid V] [Module K V] [DecidableEq β]
    (b : Basis ι K V) (label : ι → β) (blocks : Finset β) (i : ι) :
    basisLabelProjection b label blocks (b i) =
      if label i ∈ blocks then b i else 0 := by
  exact Module.Basis.constr_basis b K _ i

private theorem owner_comp_singleton
    {ι β V : Type*} {K : Type u} [Field K]
    [AddCommMonoid V] [Module K V] [Fintype β] [DecidableEq β]
    (b : Basis ι K V) (label : ι → β) {s : ℕ}
    (owner : β → Fin s) (t : Fin s) (block : β) :
    (basisLabelProjection b label
        (Finset.univ.filter (fun b ↦ t = owner b))).comp
        (basisLabelProjection b label {block}) =
      if t = owner block then basisLabelProjection b label {block} else 0 := by
  apply b.ext
  intro i
  rw [LinearMap.comp_apply]
  by_cases hi : label i = block
  · subst block
    rw [basis_projection_basis]
    simp only [Finset.mem_singleton, if_true]
    rw [basis_projection_basis]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases howned : t = owner (label i)
    · rw [if_pos howned, if_pos howned, basis_projection_basis]
      simp
    · rw [if_neg howned, if_neg howned, LinearMap.zero_apply]
  · rw [basis_projection_basis]
    simp only [Finset.mem_singleton, hi, if_false, map_zero]
    by_cases howned : t = owner block <;>
      simp [howned, basis_projection_basis, hi]

private theorem z_only_comp
    {K : Type u} [Field K] {V : Fin 3 → Type*}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
    (p q : V 2 →ₗ[K] V 2) (x : PiTensorProduct K V) :
    PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) 2 p)
        (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2 q) x) =
      PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2 (p.comp q)) x := by
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem z_only_zero
    {K : Type u} [Field K] {V : Fin 3 → Type*}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
    (x : PiTensorProduct K V) :
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2 (0 : V 2 →ₗ[K] V 2)) x = 0 := by
  have hzero := PiTensorProduct.map_update_smul
    (fun _ ↦ LinearMap.id : ∀ i, V i →ₗ[K] V i)
    (2 : Fin 3) (0 : K) LinearMap.id
  have h := LinearMap.congr_fun hzero x
  simp only [zero_smul, LinearMap.zero_apply] at h
  exact h

theorem solution
    {K : Type u} [Field K] (X : TensorObj K 3)
    {ι β : Type*} [Fintype β] [DecidableEq β]
    (b : Basis ι K (X.V 2)) (label : ι → β) {s : ℕ}
    (owner : β → Fin s) (t : Fin s) (block : β) :
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (basisLabelProjection b label
            (Finset.univ.filter (fun b ↦ t = owner b))))
        (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label {block})) X.t) =
      if t = owner block then
        PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label {block})) X.t
      else 0 := by
  rw [z_only_comp, owner_comp_singleton]
  split_ifs
  · rfl
  · exact z_only_zero X.t
