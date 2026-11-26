-- Prove2me | solution 1 for image_starRingEnd_centeredNumericalRadiusMinimizers_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:00.651858+00:00
-- url     : https://prove2.me/submissions/408a302a-01ec-4764-a0c3-e3b53e9448b9

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_centeredNumericalRadiusMinimizers_adjoint

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A =
      centeredNumericalRadiusMinimizers A := by
  rw [← centeredNumericalRadiusMinimizers_adjoint A, hA.adjoint_eq]
