-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_two_rpow_neg_movingRankBuffer_eq
-- name    : FirstPassageLinearTransport.two_rpow_neg_movingRankBuffer_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:25.875533+00:00
-- url     : https://prove2.me/theorems/49f45242-12c5-49ba-bbc6-5c22cc73c4ed
-- title:
--   First Passage Linear Transport: two rpow neg moving Rank Buffer eq
-- statement:
--   Exact exponential interpretation of the critical rank buffer.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L238-L281
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L238-L281

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.two_rpow_neg_movingRankBuffer_eq
    (A : ℕ → ℝ) (M : ℕ) :
    (2 : ℝ) ^ (-(movingRankBuffer A M)) =
      Real.sqrt ((M : ℝ) + 2) * Real.log ((M : ℝ) + 3) *
        Real.exp (-(firstPassageEndpointRate *
          (movingTerminalRank A M : ℝ))) := by sorry
