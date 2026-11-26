-- Prove2me | solution 1 for continuous_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:30:12.481014+00:00
-- url     : https://prove2.me/submissions/ff620978-eff1-46c7-8c25-be5e4221216f

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
import Theorems.Thm_lipschitzWith_numericalRadius

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution :
    Continuous (numericalRadius : (E →L[ℂ] E) → ℝ) :=
  lipschitzWith_numericalRadius.continuous
