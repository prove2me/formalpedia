-- Prove2me | solution 1 for continuous_numericalRadius_sub_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:58.874243+00:00
-- url     : https://prove2.me/submissions/1dba1528-89ed-43f4-931b-ce561974036c

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_lipschitzWith_numericalRadius_sub_smul_one

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution (A : E →L[ℂ] E) :
    Continuous (fun c : ℂ => numericalRadius (A - c • 1)) :=
  (lipschitzWith_numericalRadius_sub_smul_one A).continuous
