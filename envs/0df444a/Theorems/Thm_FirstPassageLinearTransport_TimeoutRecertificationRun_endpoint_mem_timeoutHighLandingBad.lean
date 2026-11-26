-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_endpoint_mem_timeoutHighLandingBad
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_mem_timeoutHighLandingBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:23.141145+00:00
-- url     : https://prove2.me/theorems/d6e30b64-c396-4150-aed4-7f132326210a
-- title:
--   Timeout Recertification Run: endpoint mem timeout High Landing Bad
-- statement:
--   A failed high certification at a reached threshold is literal membership
--   in the corresponding high landing target.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutExecution.lean#L38-L56
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutExecution.lean#L38-L56

import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_mem_timeoutHighLandingBad
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hbad : orbit elapsed n ∉
      initialWindowGood (timeoutHighTargetTolerance P M q)) :
    orbit elapsed n ∈
      landingBad q (timeoutHighTargetTolerance P M q) := by sorry
