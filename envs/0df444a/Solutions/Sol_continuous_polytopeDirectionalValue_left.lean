-- Prove2me | solution 1 for continuous_polytopeDirectionalValue_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:52.303956+00:00
-- url     : https://prove2.me/submissions/e8ac38fa-62bf-4b85-a1ae-f1287d8183f4

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope

set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate
theorem _root_.solution (theta : ℝ) :
    Continuous (fun z : ℂ => polytopeDirectionalValue z theta) := by
  unfold polytopeDirectionalValue
  exact (continuous_re.mul continuous_const).add
    (continuous_im.mul continuous_const)
