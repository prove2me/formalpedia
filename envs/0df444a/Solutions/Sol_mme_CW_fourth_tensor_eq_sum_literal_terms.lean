-- Prove2me | solution 1 for mme_CW_fourth_tensor_eq_sum_literal_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:03:41.027419+00:00
-- url     : https://prove2.me/submissions/0426d7d9-4aaa-40e1-bd45-db550081ef36

import Theorems.Thm_mme_CWTensor_eq_sum_literal_terms
import Definitions.Def_mme_CW_fourth_literal_support_words

open MME TensorProduct PiTensorProduct BigOperators Module

universe u

namespace MME.StothersFourth

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

private theorem interchange_sum_right
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (f : ι → PiTensorProduct K W) :
    interchange x (∑ i, f i) = ∑ i, interchange x (f i) := by
  exact map_sum (interchange x) f Finset.univ

private theorem interchange_sum_left
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ι → PiTensorProduct K V) (y : PiTensorProduct K W) :
    interchange (∑ i, f i) y = ∑ i, interchange (f i) y := by
  have h :
      (interchange (∑ i, f i) :
        PiTensorProduct K W →ₗ[K]
          PiTensorProduct K (fun i => V i ⊗[K] W i)) =
        ∑ i, interchange (f i) :=
    map_sum interchange f Finset.univ
  simpa only [LinearMap.sum_apply] using congrArg (fun g => g y) h

end MME.StothersFourth

open MME.StothersFourth

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- The literal fourth CW power is the fourfold finite sum of the grouped
interchanges of literal one-factor monomials. -/
theorem solution
    (K : Type u) [Field K] (q : ℕ) :
    (cwFourthObj K q).t =
      ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
      ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
        interchange
          (interchange (cwLiteralTermMonomial K q t₁)
            (cwLiteralTermMonomial K q t₂))
          (interchange (cwLiteralTermMonomial K q t₃)
            (cwLiteralTermMonomial K q t₄)) := by
  unfold cwFourthObj
  dsimp only [TensorObj.kron, CWObj]
  rw [mme_CWTensor_eq_sum_literal_terms]
  simp only [MME.StothersFourth.interchange_sum_left,
    MME.StothersFourth.interchange_sum_right]
  rfl
