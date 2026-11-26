-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_le_terminalRank_mul
-- name    : FirstPassageLinearTransport.eventually_shrinkingSwitchRank_le_terminalRank_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:04.901228+00:00
-- url     : https://prove2.me/theorems/f338c8d6-d8f4-59b0-a63e-2f3fcb488f99
-- title:
--   First Passage Linear Transport: eventually shrinking Switch Rank le terminal Rank mul
-- statement:
--   If the moving critical-rank buffer diverges, then the logarithmic switch
--   rank is eventually bounded by a fixed multiple of the moving terminal rank.
--   The multiplier depends only on the fixed switch coefficient and the endpoint
--   rate, not on the moving schedule.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L404-L449
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L404-L449

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_shrinkingSwitchRank_le_terminalRank_mul
    {A : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop,
      (shrinkingSwitchRank C M : ℝ) ≤
        (2 * C * firstPassageEndpointRate + 1) *
          (movingTerminalRank A M : ℝ) := by sorry
