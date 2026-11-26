-- Prove2me | solution 1 for isClosed_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:44:10.478838+00:00
-- url     : https://prove2.me/submissions/4866c6bc-243f-48da-ad49-40b59e8731b5

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Compact
import Theorems.Thm_isCompact_numericalRange

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [FiniteDimensional ℂ E] (A : E →L[ℂ] E) :
    IsClosed (numericalRange A) :=
  (isCompact_numericalRange A).isClosed
