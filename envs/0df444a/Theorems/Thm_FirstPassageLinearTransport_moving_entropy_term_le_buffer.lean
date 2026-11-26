-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_moving_entropy_term_le_buffer
-- name    : FirstPassageLinearTransport.moving_entropy_term_le_buffer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:44:11.602531+00:00
-- url     : https://prove2.me/theorems/2438b996-d446-4a9e-9c9b-33f3333ce5ee
-- title:
--   First Passage Linear Transport: moving entropy term le buffer
-- statement:
--   The moving endpoint entropy term is bounded by the exact critical-buffer
--   factor, uniformly under a fixed upper bound for the shell exponent.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAsymptotics.lean#L96-L221
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAsymptotics.lean#L96-L221

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeSupportScalars
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.moving_entropy_term_le_buffer
    {A : ℕ → ℝ} {Amax D : ℝ} {M : ℕ}
    (hAmax : 0 < Amax) (hD : 0 < D)
    (hA0 : 0 ≤ A M) (hAupper : A M ≤ Amax)
    (hL : 1 ≤ movingTerminalRank A M) :
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        Real.sqrt (movingTerminalRank A M) *
        Real.exp (-((firstPassageEndpointRate -
          D / (movingTerminalRank A M : ℝ)) *
            ((movingTerminalRank A M - 1 : ℕ) : ℝ))) ≤
      (Real.sqrt (Amax / Real.log 2 + 1) *
          Real.exp (firstPassageEndpointRate + D)) *
        ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by sorry
