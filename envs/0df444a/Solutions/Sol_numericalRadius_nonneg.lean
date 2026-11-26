-- Prove2me | solution 1 for numericalRadius_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:08.35126+00:00
-- url     : https://prove2.me/submissions/34cb99a8-4529-433d-b3c5-9090f502c6a2

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    0 ≤ numericalRadius A :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
