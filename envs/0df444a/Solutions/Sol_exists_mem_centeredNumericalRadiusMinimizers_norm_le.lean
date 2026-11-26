-- Prove2me | solution 1 for exists_mem_centeredNumericalRadiusMinimizers_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:42:44.663131+00:00
-- url     : https://prove2.me/submissions/5c51d497-b8d7-407d-bdc8-f0287d8e316e

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_centeredNumericalRadiusMinimizers_nonempty
import Theorems.Thm_norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    ∃ c ∈ centeredNumericalRadiusMinimizers A,
      ‖c‖ ≤ 2 * numericalRadius A := by
  obtain ⟨c, hc⟩ := centeredNumericalRadiusMinimizers_nonempty A
  exact ⟨c, hc,
    norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers A hc⟩
