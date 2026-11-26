-- Prove2me | solution 1 for periodic_smoothSupportUnitTangent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:05.402983+00:00
-- url     : https://prove2.me/submissions/779f5741-63d0-4700-8897-42ca6b07847b

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_periodic_smoothSupportUnitNormal

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution :
    Function.Periodic smoothSupportUnitTangent (2 * Real.pi) := by
  exact periodic_smoothSupportUnitNormal.comp (fun z : ℂ => z * I)
