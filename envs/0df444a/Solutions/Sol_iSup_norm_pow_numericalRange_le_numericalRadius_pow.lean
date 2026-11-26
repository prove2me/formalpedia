-- Prove2me | solution 1 for iSup_norm_pow_numericalRange_le_numericalRadius_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:56.225261+00:00
-- url     : https://prove2.me/submissions/777e5154-d8da-4425-b5ac-a9768202f9f9

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_norm_le_numericalRadius
import Theorems.Thm_numericalRadius_nonneg


set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (n : ℕ) :
    (⨆ z ∈ numericalRange A, ‖z ^ n‖) ≤ numericalRadius A ^ n := by
  refine Real.iSup_le (fun z => ?_) (pow_nonneg (numericalRadius_nonneg A) n)
  refine Real.iSup_le (fun hz => ?_) (pow_nonneg (numericalRadius_nonneg A) n)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg z) (norm_le_numericalRadius A hz) n
