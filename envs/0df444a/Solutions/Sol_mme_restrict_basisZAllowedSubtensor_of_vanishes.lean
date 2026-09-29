-- Prove2me | solution 1 for mme_restrict_basisZAllowedSubtensor_of_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:27:05.754777+00:00
-- url     : https://prove2.me/submissions/4e411d82-9401-4a93-b93c-3abd6c0a0c33

import Mathlib
import Definitions.Def_mme_basis_z_allowed_projection
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (T A : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed]
    (f : ∀ i, T.V i →ₗ[K] A.V i)
    (hmap : PiTensorProduct.map f T.t = A.t)
    (hvanish : ∀ j, ¬ allowed j → f 2 (bZ j) = 0) :
    TensorObj.Restrict A (T.basisZAllowedSubtensor bZ allowed) := by
  let G := T.basisZAllowedGrading bZ allowed
  let projection : ∀ i : Fin 3, T.V i →ₗ[K] T.V i :=
    Function.update (fun _ ↦ LinearMap.id)
      2 (bZ.constr K (fun j ↦ if allowed j then bZ j else 0))
  have hcomp : ∀ i, (f i).comp (projection i) = f i := by
    intro i
    by_cases hi : i = 2
    · subst i
      have hprojection : projection (2 : Fin 3) =
          bZ.constr K (fun j ↦ if allowed j then bZ j else 0) := by
        simp [projection]
      rw [hprojection]
      apply bZ.ext
      intro j
      by_cases hj : allowed j
      · rw [LinearMap.comp_apply, Module.Basis.constr_basis, if_pos hj]
      · rw [LinearMap.comp_apply, Module.Basis.constr_basis, if_neg hj,
          map_zero, hvanish j hj]
    · have hprojection : projection i = LinearMap.id := by
        simp [projection, hi]
      rw [hprojection]
      ext x
      rfl
  refine ⟨fun i ↦ (f i).comp (G.classOf i 0).subtype, ?_⟩
  change PiTensorProduct.map
      (fun i ↦ (f i).comp (G.classOf i 0).subtype)
        (G.blockSubtensor (fun _ ↦ 0)).t = A.t
  have h1 : PiTensorProduct.map (fun i ↦ (f i).comp (G.classOf i 0).subtype)
        (G.blockSubtensor (fun _ ↦ 0)).t =
      PiTensorProduct.map f
        (PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
          (G.blockSubtensor (fun _ ↦ 0)).t) :=
    congrFun (congrArg DFunLike.coe
      (PiTensorProduct.map_comp f (fun i ↦ (G.classOf i 0).subtype))) _
  have h2 : PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
        (G.blockSubtensor (fun _ ↦ 0)).t =
      PiTensorProduct.map projection T.t :=
    mme_basisZAllowed_blockSubtensor_inclusion_tensor T bZ allowed
  have h2' := congrArg (fun x ↦ PiTensorProduct.map f x) h2
  have h3 : PiTensorProduct.map f (PiTensorProduct.map projection T.t) =
      PiTensorProduct.map (fun i ↦ (f i).comp (projection i)) T.t :=
    (congrFun (congrArg DFunLike.coe
      (PiTensorProduct.map_comp f projection)) _).symm
  have h4 : PiTensorProduct.map (fun i ↦ (f i).comp (projection i)) T.t =
      PiTensorProduct.map f T.t :=
    congrArg (fun F ↦ PiTensorProduct.map F T.t) (funext hcomp)
  exact h1.trans (h2'.trans (h3.trans (h4.trans hmap)))
