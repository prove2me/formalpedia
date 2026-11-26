-- Prove2me | solution 1 for crouzeix_palencia_of_strictNestedSmoothJordanExhaustion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:17.184929+00:00
-- url     : https://prove2.me/submissions/37e0d9f1-38b3-4ef5-9dbc-053ca56596ac

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
import Theorems.Thm_SmoothJordanDomain_hasMergelyanPolynomialApproximation
import Theorems.Thm_crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_hasMergelyanPolynomialApproximation


set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (Omega : StrictNestedSmoothJordanExhaustion
      (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_hasMergelyanPolynomialApproximation
      A Omega
  intro n
  exact (Omega.domain n).hasMergelyanPolynomialApproximation
