-- Prove2me | solution 1 for mme_basisZAllowedSubtensor_restrict_of_basis_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:40:29.22484+00:00
-- url     : https://prove2.me/submissions/2119e7d4-168e-41c9-8c3e-3daecde0027e

import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem basisZAllowed_blockProj_basis_eq_zero_of_not_allowed
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] (j : ι) (hj : ¬ allowed j) :
    (T.basisZAllowedGrading bZ allowed).blockProj 2 0 (bZ j) = 0 := by
  let G := T.basisZAllowedGrading bZ allowed
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne G 2 0 1
  · decide
  · change bZ j ∈ cwBasisGrade bZ
      (fun k ↦ if allowed k then 0 else 1) 1
    exact Submodule.subset_span
      ⟨j, by simp only [Set.mem_ofPred_eq, if_neg hj], rfl⟩

theorem solution
    {K : Type u} [Field K]
    (T U : TensorObj K 3) {ι κ : Type u}
    (bT : Basis ι K (T.V 2)) (bU : Basis κ K (U.V 2))
    (allowedT : ι → Prop) (allowedU : κ → Prop)
    [DecidablePred allowedT] [DecidablePred allowedU]
    (f : ∀ i : Fin 3, T.V i →ₗ[K] U.V i)
    (hmap : PiTensorProduct.map f T.t = U.t)
    (σ : ι → Option κ)
    (hNone : ∀ j, σ j = none → f 2 (bT j) = 0)
    (hSome : ∀ j k, σ j = some k → f 2 (bT j) = bU k)
    (hAllowed : ∀ j k, σ j = some k →
      (allowedT j ↔ allowedU k)) :
    TensorObj.Restrict
      (U.basisZAllowedSubtensor bU allowedU)
      (T.basisZAllowedSubtensor bT allowedT) := by
  let GU := U.basisZAllowedGrading bU allowedU
  let g : ∀ i : Fin 3,
      T.V i →ₗ[K] (GU.classOf i 0 : Submodule K (U.V i)) :=
    fun i ↦ (GU.blockProj i 0).comp (f i)
  apply mme_restrict_basisZAllowedSubtensor_of_vanishes
    T (U.basisZAllowedSubtensor bU allowedU)
      bT allowedT g
  · change PiTensorProduct.map g T.t =
      (GU.blockSubtensor (fun _ ↦ 0)).t
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hmap]
    rfl
  · intro j hj
    cases hσ : σ j with
    | none =>
        change GU.blockProj 2 0 (f 2 (bT j)) = 0
        rw [hNone j hσ, map_zero]
    | some k =>
        have hk : ¬ allowedU k := by
          intro hk
          exact hj ((hAllowed j k hσ).mpr hk)
        change GU.blockProj 2 0 (f 2 (bT j)) = 0
        rw [hSome j k hσ]
        exact basisZAllowed_blockProj_basis_eq_zero_of_not_allowed
          U bU allowedU k hk
