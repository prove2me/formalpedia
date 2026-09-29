-- Prove2me | solution 1 for mme_tensorProduct_basis_filter_absorption
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:18:35.486192+00:00
-- url     : https://prove2.me/submissions/4210bcda-3f30-40a2-911b-4016f2192171

import Mathlib.LinearAlgebra.TensorProduct.Basis

open Module TensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {V W U : Type u}
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U]
    {iota kappa : Type u}
    (bV : Basis iota K V) (bW : Basis kappa K W)
    (allowedV : iota → Prop) (allowedW : kappa → Prop)
    [DecidablePred allowedV] [DecidablePred allowedW]
    (f : (V ⊗[K] W) →ₗ[K] U)
    (hvanish : ∀ (i : iota) (j : kappa),
      ¬ allowedV i ∨ ¬ allowedW j →
        f (bV i ⊗ₜ[K] bW j) = 0) :
    f.comp (TensorProduct.map
      (bV.constr K (fun i ↦ if allowedV i then bV i else 0))
      (bW.constr K (fun j ↦ if allowedW j then bW j else 0))) = f := by
  apply (Module.Basis.tensorProduct bV bW).ext
  rintro ⟨i, j⟩
  rw [Module.Basis.tensorProduct_apply', LinearMap.comp_apply,
    TensorProduct.map_tmul, Basis.constr_basis, Basis.constr_basis]
  by_cases hi : allowedV i
  · by_cases hj : allowedW j
    · simp [hi, hj]
    · simp [hi, hj, hvanish i j (Or.inr hj)]
  · simp [hi, hvanish i j (Or.inl hi)]
