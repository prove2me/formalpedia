-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sharp_timeout_scalar_le_buffer
-- name    : FirstPassageLinearTransport.sharp_timeout_scalar_le_buffer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:24.791534+00:00
-- url     : https://prove2.me/theorems/16b37da7-1231-4288-9629-b0d077277f6d
-- title:
--   First Passage Linear Transport: sharp timeout scalar le buffer
-- statement:
--   The Version 4 timeout scalar is paid directly by the sharp critical
--   buffer.  The square-root support cost cancels against the terminal
--   `L⁻¹ᐟ²` ballot prefactor.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L158-L235
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L158-L235

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.sharp_timeout_scalar_le_buffer
    {A : ℕ → ℝ} {M : ℕ}
    (hbuf : 0 ≤ sharpMovingRankBuffer A M)
    (hL : 1 ≤ movingTerminalRank A M) :
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        (1 / Real.sqrt (movingTerminalRank A M)) *
        Real.exp (-(firstPassageEndpointRate *
          (movingTerminalRank A M : ℝ))) ≤
      Real.sqrt (2 * firstPassageEndpointRate) *
        (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) := by sorry
