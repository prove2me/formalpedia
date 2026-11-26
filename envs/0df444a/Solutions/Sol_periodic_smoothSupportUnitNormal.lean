-- Prove2me | solution 1 for periodic_smoothSupportUnitNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:02.446733+00:00
-- url     : https://prove2.me/submissions/7ee134d9-4382-4c6c-ae3e-74955d326f6a

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution :
    Function.Periodic smoothSupportUnitNormal (2 * Real.pi) := by
  exact periodic_circleMap 0 1
