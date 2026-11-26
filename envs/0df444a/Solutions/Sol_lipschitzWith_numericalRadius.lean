-- Prove2me | solution 1 for lipschitzWith_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:32.135309+00:00
-- url     : https://prove2.me/submissions/2c0764a1-d88f-4856-ba09-4660e52040b9

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_abs_numericalRadius_sub_le_norm
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


attribute [local simp] numericalRadius_neg
attribute [local simp] numericalRadiusSeminorm_apply

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution :
    LipschitzWith 1 (numericalRadius : (E →L[ℂ] E) → ℝ) := by
  apply LipschitzWith.mk_one
  intro A B
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
    abs_numericalRadius_sub_le_norm A B
