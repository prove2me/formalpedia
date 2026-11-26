-- Prove2me | solution 1 for exists_imaginary_center_minimizing_numericalRadius_of_mem_skewAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:08.70031+00:00
-- url     : https://prove2.me/submissions/ce8d7fb2-a73a-4feb-89c9-64541df04eb2

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_exists_imaginary_mem_centeredNumericalRadiusMinimizers

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    ∃ r : ℝ, ∀ c : ℂ,
      numericalRadius (A - ((r : ℂ) * Complex.I) • 1) ≤
        numericalRadius (A - c • 1) := by
  exact exists_imaginary_mem_centeredNumericalRadiusMinimizers A hA
