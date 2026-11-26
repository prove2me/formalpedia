-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutOddDisplacement_gt_endpoint_sub_div
-- name    : FirstPassageLinearTransport.timeoutOddDisplacement_gt_endpoint_sub_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:25:22.767074+00:00
-- url     : https://prove2.me/theorems/672d3d95-5944-5944-9e13-31f47ccb7471
-- title:
--   First Passage Linear Transport: timeout Odd Displacement gt endpoint sub div
-- statement:
--   Uniform lower approach of the exact timeout displacement to the endpoint
--   displacement.  Only `m ≥ L` is used; no upper rank window enters this scalar
--   estimate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L580-L644
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L580-L644

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutOddDisplacement_gt_endpoint_sub_div
    {K₀ : ℝ} {L m : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L) (hLm : L ≤ m) :
    firstPassageEndpointDisplacement -
        timeoutDisplacementLoss K₀ / (L : ℝ) <
      timeoutOddDisplacement K₀ L m := by sorry
