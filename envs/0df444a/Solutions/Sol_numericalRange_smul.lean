-- Prove2me | solution 1 for numericalRange_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:03.402859+00:00
-- url     : https://prove2.me/submissions/44c948e6-38a6-4a3a-9d28-16c400d55f6b

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
    numericalRange (c • A) =
      (fun z => c * z) '' numericalRange A := by
  simpa only [zero_smul, sub_zero, sub_zero] using
    numericalRange_smul_sub_smul_one A c 0
