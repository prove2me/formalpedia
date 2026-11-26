-- Prove2me | solution 1 for numericalRadius_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:16:49.078557+00:00
-- url     : https://prove2.me/submissions/b0c078fe-60eb-4762-a940-a3f5e03c29e9

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRadius (-A) = numericalRadius A := by
  rw [← neg_one_smul ℂ A, numericalRadius_smul, norm_neg, norm_one, one_mul]
