-- Prove2me | solution 1 for numericalRange_smul_sub_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:50.00159+00:00
-- url     : https://prove2.me/submissions/4e463a5c-c2d4-4a9a-bb61-798308be7fa3

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
import Theorems.Thm_inner_smul_sub_smul_one_apply_self
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c z₀ : ℂ) :
    numericalRange (c • (A - z₀ • 1)) =
      (fun z => c * (z - z₀)) '' numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).2 ⟨x, hx, rfl⟩, ?_⟩
    exact (inner_smul_sub_smul_one_apply_self c z₀ A hx).symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_numericalRange A w).1 hw
    refine (mem_numericalRange _ _).2 ⟨x, hx, ?_⟩
    exact inner_smul_sub_smul_one_apply_self c z₀ A hx
