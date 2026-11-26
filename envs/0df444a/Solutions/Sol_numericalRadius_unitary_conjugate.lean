-- Prove2me | solution 1 for numericalRadius_unitary_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:51.508516+00:00
-- url     : https://prove2.me/submissions/152a2444-0e37-42b2-bf46-607009096f6b

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Theorems.Thm_numericalRange_unitary_conjugate

set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius (U† * A * U) = numericalRadius A := by
  unfold numericalRadius
  rw [numericalRange_unitary_conjugate A U hU]
