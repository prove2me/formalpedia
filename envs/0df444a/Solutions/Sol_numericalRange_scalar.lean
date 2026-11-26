-- Prove2me | solution 1 for numericalRange_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:01.511109+00:00
-- url     : https://prove2.me/submissions/7e1f642e-42cb-4e09-8101-4f42f960f535

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
import Theorems.Thm_numericalRange_add_smul_one
import Theorems.Thm_numericalRange_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


attribute [local simp] numericalRange_zero

set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [Nontrivial E] (c : ℂ) :
    numericalRange (c • (1 : E →L[ℂ] E)) = {c} := by
  have h := numericalRange_add_smul_one (0 : E →L[ℂ] E) c
  simpa only [zero_add, numericalRange_zero, image_singleton, zero_add] using h
