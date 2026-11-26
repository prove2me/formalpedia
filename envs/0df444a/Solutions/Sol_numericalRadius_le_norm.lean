-- Prove2me | solution 1 for numericalRadius_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:13.521506+00:00
-- url     : https://prove2.me/submissions/1fab94b0-13be-406c-9d02-a184af3912eb

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
import Theorems.Thm_norm_le_of_mem_numericalRange

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRadius A ≤ ‖A‖ := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_) (norm_nonneg A)
  exact Real.iSup_le
    (fun hz => norm_le_of_mem_numericalRange A hz) (norm_nonneg A)
