-- Prove2me | solution 1 for norm_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:29:08.564179+00:00
-- url     : https://prove2.me/submissions/e5d89b08-9a85-4bdb-aa81-44c2a4889a0f

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_norm_le_one_add_sqrt_two_mul_numericalRadius

set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    ‖A - c • (1 : E →L[ℂ] E)‖ ≤
      (1 + Real.sqrt 2) *
        numericalRadius (A - c • (1 : E →L[ℂ] E)) :=
  norm_le_one_add_sqrt_two_mul_numericalRadius
    (A - c • (1 : E →L[ℂ] E))
