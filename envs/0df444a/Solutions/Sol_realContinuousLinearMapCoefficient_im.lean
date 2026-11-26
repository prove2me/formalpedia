-- Prove2me | solution 1 for realContinuousLinearMapCoefficient_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:08.933305+00:00
-- url     : https://prove2.me/submissions/0153f584-a9a5-47fd-9f8f-187a0a07eeb1

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_PlanarDualDirection

set_option autoImplicit false
open Complex
theorem _root_.solution
    (f : ℂ →L[ℝ] ℝ) :
    (realContinuousLinearMapCoefficient f).im = f I := rfl
