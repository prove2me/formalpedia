-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_le_terminalRank_mul_of_sharp
-- name    : FirstPassageLinearTransport.eventually_shrinkingSwitchRank_le_terminalRank_mul_of_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:44.09875+00:00
-- url     : https://prove2.me/theorems/75726324-3ce7-4e1f-8c17-301e82a8a120
-- title:
--   First Passage Linear Transport: eventually shrinking Switch Rank le terminal Rank mul of sharp
-- statement:
--   Sharp-buffer version of the uniform low-window comparison.  Unlike the
--   Version 3 route, this requires no secondary logarithmic debit.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L453-L490
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L453-L490

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_shrinkingSwitchRank_le_terminalRank_mul_of_sharp
    {A : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop,
      (shrinkingSwitchRank C M : ℝ) ≤
        (2 * C * firstPassageEndpointRate + 1) *
          (movingTerminalRank A M : ℝ) := by sorry
