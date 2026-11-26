-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutDisplacementLoss_le_terminalScale
-- name    : FirstPassageLinearTransport.eventually_timeoutDisplacementLoss_le_terminalScale
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:46:32.690965+00:00
-- url     : https://prove2.me/theorems/3b9782a7-f4f8-56dd-959f-9952c5abb12e
-- title:
--   First Passage Linear Transport: eventually timeout Displacement Loss le terminal Scale
-- statement:
--   The explicit timeout displacement loss is eventually paid by the
--   terminal rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L26-L36
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean#L26-L36

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutDisplacementLoss_le_terminalScale
    (K₀ : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      2 * timeoutDisplacementLoss K₀ ≤
        firstPassageEndpointDisplacement * (L : ℝ) := by sorry
