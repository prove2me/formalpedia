-- Prove2me | solution 1 for tendsto_numericalRadius_sub_smul_one_cocompact_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:56.708053+00:00
-- url     : https://prove2.me/submissions/ebc01938-431b-4285-83dc-76bfc2e508c4

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_norm_sub_numericalRadius_le_numericalRadius_sub_smul_one

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    Tendsto (fun c : ℂ => numericalRadius (A - c • 1))
      (cocompact ℂ) atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards
      [tendsto_norm_cocompact_atTop.eventually
        (eventually_ge_atTop (b + numericalRadius A))] with c hc
  exact le_trans (by linarith)
    (norm_sub_numericalRadius_le_numericalRadius_sub_smul_one A c)
