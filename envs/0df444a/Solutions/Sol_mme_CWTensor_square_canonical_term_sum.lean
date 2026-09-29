-- Prove2me | solution 1 for mme_CWTensor_square_canonical_term_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:10:47.668378+00:00
-- url     : https://prove2.me/submissions/b7c1aa47-57f5-4ebd-9cac-29dff17e27bf

import Definitions.Def_mme_stothers_phi116_term_expansion
import Theorems.Thm_mme_CWTensor_canonical_term_sum

open MME TensorProduct Module BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem interchange_sum_right
    {K : Type u} [Field K] {d : ℕ} {iota : Type*} [Fintype iota]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (f : iota → PiTensorProduct K W) :
    interchange x (∑ i, f i) = ∑ i, interchange x (f i) := by
  exact map_sum (interchange x) f Finset.univ

private theorem interchange_sum_left
    {K : Type u} [Field K] {d : ℕ} {iota : Type*} [Fintype iota]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : iota → PiTensorProduct K V) (y : PiTensorProduct K W) :
    interchange (∑ i, f i) y = ∑ i, interchange (f i) y := by
  have h :
      (interchange (∑ i, f i) :
        PiTensorProduct K W →ₗ[K]
          PiTensorProduct K (fun i => V i ⊗[K] W i)) =
        ∑ i, interchange (f i) :=
    map_sum interchange f Finset.univ
  simpa only [LinearMap.coe_sum, Finset.sum_apply] using
    congrArg (fun g => g y) h

theorem solution
    (K : Type u) [Field K] (q : ℕ) :
    interchange (CWTensor K q) (CWTensor K q) =
      ∑ t₂ : MME.StothersFourth.Phi116.CWTerm q,
      ∑ t₁ : MME.StothersFourth.Phi116.CWTerm q,
        interchange
          (MME.StothersFourth.Phi116.cwTermMonom K q t₁)
          (MME.StothersFourth.Phi116.cwTermMonom K q t₂) := by
  rw [mme_CWTensor_canonical_term_sum K q]
  simp only [interchange_sum_left, interchange_sum_right]
