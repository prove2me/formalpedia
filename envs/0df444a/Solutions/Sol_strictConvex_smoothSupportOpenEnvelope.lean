-- Prove2me | solution 1 for strictConvex_smoothSupportOpenEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:37.321374+00:00
-- url     : https://prove2.me/submissions/091a6dcf-50ea-4bc9-aa0c-371057564988

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Theorems.Thm_isOpen_smoothSupportOpenEnvelope
import Theorems.Thm_convex_smoothSupportOpenEnvelope

set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate
theorem _root_.solution (h : ℝ → ℝ) :
    StrictConvex ℝ (smoothSupportOpenEnvelope h) :=
  (convex_smoothSupportOpenEnvelope h).strictConvex_of_isOpen
    (isOpen_smoothSupportOpenEnvelope h)
