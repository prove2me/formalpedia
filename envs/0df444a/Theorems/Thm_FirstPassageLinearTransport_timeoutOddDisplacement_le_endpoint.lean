-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutOddDisplacement_le_endpoint
-- name    : FirstPassageLinearTransport.timeoutOddDisplacement_le_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:25:29.214035+00:00
-- url     : https://prove2.me/theorems/d6f6cecd-f2f9-4024-ac96-b06fda3b3199
-- title:
--   First Passage Linear Transport: timeout Odd Displacement le endpoint
-- statement:
--   The exact timeout displacement never exceeds the endpoint displacement
--   when the moving ratio lies in `[0,1]`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L648-L684
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L648-L684

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutOddDisplacement_le_endpoint
    {K₀ : ℝ} {L m : ℕ}
    (hr0 : 0 ≤ movingLowRatio K₀ L)
    (hr1 : movingLowRatio K₀ L ≤ 1)
    (hm : 0 < m) :
    timeoutOddDisplacement K₀ L m ≤
      firstPassageEndpointDisplacement := by sorry
