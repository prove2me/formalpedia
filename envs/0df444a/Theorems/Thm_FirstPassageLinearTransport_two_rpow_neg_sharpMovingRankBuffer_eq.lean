-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_two_rpow_neg_sharpMovingRankBuffer_eq
-- name    : FirstPassageLinearTransport.two_rpow_neg_sharpMovingRankBuffer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:20.90984+00:00
-- url     : https://prove2.me/theorems/657fd06f-6700-4390-a5f2-e30cb9512358
-- title:
--   First Passage Linear Transport: two rpow neg sharp Moving Rank Buffer eq
-- statement:
--   Exact exponential interpretation of the Version 4 critical buffer.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L119-L153
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L119-L153

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.two_rpow_neg_sharpMovingRankBuffer_eq
    (A : ℕ → ℝ) (M : ℕ) :
    (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) =
      Real.sqrt ((M : ℝ) + 2) *
        Real.exp (-(firstPassageEndpointRate *
          (movingTerminalRank A M : ℝ))) := by sorry
