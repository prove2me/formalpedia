-- Prove2me | solution 1 for hasSmoothJordanOuterApproximationForPolytopes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:35.957139+00:00
-- url     : https://prove2.me/submissions/199ba6aa-9d9a-4830-b333-0f8b5c46eea2

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Theorems.Thm_hasSmoothJordanOuterApproximationForPolytopes_of_supportCurve_range
import Theorems.Thm_range_polytopeRoundedSupportCurve_eq_frontier


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
theorem _root_.solution :
    HasSmoothJordanOuterApproximationForPolytopes := by
  apply
    hasSmoothJordanOuterApproximationForPolytopes_of_supportCurve_range
  intro u hu delta rho hdelta hrho
  exact range_polytopeRoundedSupportCurve_eq_frontier hu hdelta hrho
