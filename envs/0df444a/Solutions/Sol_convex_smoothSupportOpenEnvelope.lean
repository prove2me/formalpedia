-- Prove2me | solution 1 for convex_smoothSupportOpenEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:05.330009+00:00
-- url     : https://prove2.me/submissions/9f65d40c-09b3-4b9b-a5f1-1034af8c2425

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Theorems.Thm_convex_smoothSupportClosedEnvelope

set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate
theorem _root_.solution (h : ℝ → ℝ) :
    Convex ℝ (smoothSupportOpenEnvelope h) :=
  (convex_smoothSupportClosedEnvelope h).interior
