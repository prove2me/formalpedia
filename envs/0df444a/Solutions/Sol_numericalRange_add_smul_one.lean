-- Prove2me | solution 1 for numericalRange_add_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:25.178619+00:00
-- url     : https://prove2.me/submissions/a26753ff-9b73-48f7-86f1-b537b6446984

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
import Theorems.Thm_numericalRange_sub_smul_one
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) (c : ℂ) :
    numericalRange (A + c • 1) =
      (fun z => z + c) '' numericalRange A := by
  simpa only [sub_neg_eq_add, neg_smul] using
    numericalRange_sub_smul_one A (-c)
