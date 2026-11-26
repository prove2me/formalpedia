-- Prove2me | solution 1 for hasDerivAt_smoothSupportUnitTangent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:23.399284+00:00
-- url     : https://prove2.me/submissions/755f020a-15c0-448d-8181-b39e3abb3b90

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_contDiff_smoothSupportUnitTangent
import Theorems.Thm_deriv_smoothSupportUnitTangent

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution (theta : ℝ) :
    HasDerivAt smoothSupportUnitTangent
      (-smoothSupportUnitNormal theta) theta := by
  have hdiff :=
    (contDiff_smoothSupportUnitTangent.differentiable (by norm_num) theta).hasDerivAt
  rwa [deriv_smoothSupportUnitTangent] at hdiff
