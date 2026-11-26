-- Prove2me | solution 1 for isCompact_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:36.835377+00:00
-- url     : https://prove2.me/submissions/743cb93b-413a-48e2-943f-47f66ca43410

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Compact
import Theorems.Thm_numericalRange_eq_image

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [FiniteDimensional ℂ E] (A : E →L[ℂ] E) :
    IsCompact (numericalRange A) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  rw [numericalRange_eq_image]
  exact (isCompact_sphere (0 : E) 1).image (continuous_id.inner A.continuous)
