-- Prove2me | solution 1 for numericalRadius_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:30:05.049264+00:00
-- url     : https://prove2.me/submissions/d6907542-8c7f-403a-966e-215e2976ccb2

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadius_nonneg
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    0 < numericalRadius A ↔ A ≠ 0 := by
  rw [(numericalRadius_nonneg A).lt_iff_ne]
  simpa only [ne_eq, eq_comm] using
    not_congr (numericalRadius_eq_zero_iff A)
