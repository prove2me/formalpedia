-- Prove2me | solution 1 for polynomialSupNorm_closure_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:36.953465+00:00
-- url     : https://prove2.me/submissions/718f1817-3869-4111-8ff0-815da013ece4

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_isBounded_numericalRange
import Theorems.Thm_polynomialSupNorm_closure_of_isBounded


set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (p : ℂ[X]) :
    polynomialSupNorm p (closure (numericalRange A)) =
      polynomialSupNorm p (numericalRange A) :=
  polynomialSupNorm_closure_of_isBounded p (isBounded_numericalRange A)
