-- Prove2me | solution 1 for isBounded_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:34.00442+00:00
-- url     : https://prove2.me/submissions/c6f315a1-b8bd-4f91-a3da-7faad82167de

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
import Theorems.Thm_numericalRange_subset_closedBall

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    Bornology.IsBounded (numericalRange A) :=
  Metric.isBounded_closedBall.subset (numericalRange_subset_closedBall A)
