-- Prove2me | solution 1 for hasSmoothJordanOuterApproximation_closure_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:38.81378+00:00
-- url     : https://prove2.me/submissions/ab68a32f-db5a-45dc-a0a6-9aa7fcc076cf

import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_SmoothSupportExhaustion
import Theorems.Thm_convex_numericalRange


set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    HasSmoothJordanOuterApproximation (closure (numericalRange A)) :=
  hasSmoothJordanOuterApproximation_of_isCompact_nonempty_convex
    (isCompact_closure_numericalRange A)
    (nonempty_closure_numericalRange A)
    (convex_numericalRange A).closure
