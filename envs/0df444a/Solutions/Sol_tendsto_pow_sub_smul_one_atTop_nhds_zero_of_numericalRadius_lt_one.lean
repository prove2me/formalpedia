-- Prove2me | solution 1 for tendsto_pow_sub_smul_one_atTop_nhds_zero_of_numericalRadius_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:29:27.524647+00:00
-- url     : https://prove2.me/submissions/6c89281a-a306-4ccc-bb2d-0bd156094c96

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_tendsto_pow_atTop_nhds_zero_of_numericalRadius_lt_one

set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ)
    (hA : numericalRadius (A - c • (1 : E →L[ℂ] E)) < 1) :
    Filter.Tendsto
      (fun n : ℕ => (A - c • (1 : E →L[ℂ] E)) ^ n)
      Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_numericalRadius_lt_one
    (A - c • (1 : E →L[ℂ] E)) hA
