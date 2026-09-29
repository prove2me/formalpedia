-- Prove2me | solution 1 for mme_dwz_basisLabelProjection_singleton_tensor_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:02:00.025521+00:00
-- url     : https://prove2.me/submissions/225db219-5a2a-44d5-b270-f4ef43aa4517

import Definitions.Def_mme_dwz_basis_label_projection
import Mathlib.Tactic.FinCases

open MME Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem singleton_intertwine
    {K : Type u} [Field K]
    {ι β V : Type*} [AddCommMonoid V] [Module K V]
    [DecidableEq β]
    (b : Basis ι K V) (label : ι → β)
    (F : V ≃ₗ[K] V) (move : Equiv.Perm β)
    (hF : ∀ x, ∃ y,
      F (b x) = b y ∧ label y = move (label x))
    (block : β) :
    F.toLinearMap.comp (basisLabelProjection b label {block}) =
      (basisLabelProjection b label {move block}).comp F.toLinearMap := by
  apply b.ext
  intro x
  obtain ⟨y, hFxy, hlabel⟩ := hF x
  have hFxy' : F.toLinearMap (b x) = b y := hFxy
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold basisLabelProjection
  rw [Module.Basis.constr_basis]
  simp only [Finset.mem_singleton]
  by_cases hx : label x = block
  · rw [if_pos hx]
    rw [hFxy', Module.Basis.constr_basis]
    have hy : label y = move block := hlabel.trans (congrArg move hx)
    rw [if_pos hy]
  · rw [if_neg hx, map_zero]
    rw [hFxy', Module.Basis.constr_basis]
    rw [if_neg]
    intro hy
    apply hx
    apply move.injective
    exact hlabel.symm.trans hy

theorem solution
    {K : Type u} [Field K]
    (X : TensorObj K 3) {ι β : Type u} [DecidableEq β]
    (b : Basis ι K (X.V 2)) (label : ι → β)
    (F : ∀ i, X.V i ≃ₗ[K] X.V i) (move : Equiv.Perm β)
    (hTensor :
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap) X.t = X.t)
    (hF : ∀ x, ∃ y,
      F 2 (b x) = b y ∧ label y = move (label x))
    (block : β) :
    PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label {block})) X.t) =
      PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (basisLabelProjection b label {move block})) X.t := by
  let before := Function.update (fun _ ↦ LinearMap.id) 2
    (basisLabelProjection b label {block})
  let after := Function.update (fun _ ↦ LinearMap.id) 2
    (basisLabelProjection b label {move block})
  calc
    PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (PiTensorProduct.map before X.t) =
        PiTensorProduct.map
          (fun i ↦ (F i).toLinearMap.comp (before i)) X.t := by
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    _ = PiTensorProduct.map
          (fun i ↦ (after i).comp (F i).toLinearMap) X.t := by
      congr 2
      funext i
      fin_cases i
      · simp only [before, after, Function.update]
        ext x
        rfl
      · simp only [before, after, Function.update]
        ext x
        rfl
      · simpa [before, after] using
          singleton_intertwine b label (F 2) move hF block
    _ = PiTensorProduct.map after
          (PiTensorProduct.map (fun i ↦ (F i).toLinearMap) X.t) := by
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    _ = PiTensorProduct.map after X.t := by rw [hTensor]
