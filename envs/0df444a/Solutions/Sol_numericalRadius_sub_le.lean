-- Prove2me | solution 1 for numericalRadius_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:39.277072+00:00
-- url     : https://prove2.me/submissions/8bceee86-c7ee-4cc5-9542-0f1d7ef4f4e1

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


attribute [local simp] numericalRadius_neg

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A B : E →L[ℂ] E) :
    numericalRadius (A - B) ≤ numericalRadius A + numericalRadius B := by
  rw [sub_eq_add_neg]
  exact (numericalRadius_add_le A (-B)).trans_eq
    (congrArg (numericalRadius A + ·) (numericalRadius_neg B))
