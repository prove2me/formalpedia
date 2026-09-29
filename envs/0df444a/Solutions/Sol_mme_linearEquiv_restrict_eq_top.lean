-- Prove2me | solution 1 for mme_linearEquiv_restrict_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:37:50.58174+00:00
-- url     : https://prove2.me/submissions/f53568a9-a9f5-46fe-8d39-fc61983e13dc

import Mathlib.LinearAlgebra.PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (C : Submodule K V) (hC : C = ⊤) (P : V ≃ₗ[K] V) :
    ∃ E : C ≃ₗ[K] C,
      (Submodule.subtype C).comp E.toLinearMap =
        P.toLinearMap.comp (Submodule.subtype C) := by
  have htop_le : (⊤ : Submodule K V) ≤ C := by
    rw [hC]
  let E : C ≃ₗ[K] C :=
    { toFun := fun x ↦ ⟨P x.1, htop_le Submodule.mem_top⟩
      invFun := fun x ↦ ⟨P.symm x.1, htop_le Submodule.mem_top⟩
      left_inv := by
        intro x
        ext
        exact P.symm_apply_apply x.1
      right_inv := by
        intro x
        ext
        exact P.apply_symm_apply x.1
      map_add' := by
        intro x y
        ext
        exact P.map_add x.1 y.1
      map_smul' := by
        intro c x
        ext
        exact P.map_smul c x.1 }
  refine ⟨E, ?_⟩
  ext x
  rfl
