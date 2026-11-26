-- Prove2me | solution 1 for isOpen_smoothSupportOpenEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:57.145094+00:00
-- url     : https://prove2.me/submissions/3db8010e-b452-42f8-b180-bb7ae30321b4

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope

set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate
theorem _root_.solution (h : ℝ → ℝ) :
    IsOpen (smoothSupportOpenEnvelope h) :=
  isOpen_interior
