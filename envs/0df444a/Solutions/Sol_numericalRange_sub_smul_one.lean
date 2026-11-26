-- Prove2me | solution 1 for numericalRange_sub_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:30.769955+00:00
-- url     : https://prove2.me/submissions/88e50849-b97a-4d20-8f87-914174d33fcf

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
import Theorems.Thm_numericalRange_smul_sub_smul_one
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) (c : ℂ) :
    numericalRange (A - c • 1) =
      (fun z => z - c) '' numericalRange A := by
  simpa only [one_smul, one_mul] using
    numericalRange_smul_sub_smul_one A 1 c
