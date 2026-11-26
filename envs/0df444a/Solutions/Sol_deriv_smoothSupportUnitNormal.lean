-- Prove2me | solution 1 for deriv_smoothSupportUnitNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:56.058646+00:00
-- url     : https://prove2.me/submissions/1ed58d9f-a722-4b08-8bcb-aee32e7b234b

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution (theta : ℝ) :
    deriv smoothSupportUnitNormal theta =
      smoothSupportUnitTangent theta := by
  unfold smoothSupportUnitNormal smoothSupportUnitTangent
  exact deriv_circleMap 0 1 theta
