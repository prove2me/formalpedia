-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellBad_timeoutEndpointGood
-- name    : FirstPassageLinearTransport.shellBad_timeoutEndpointGood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:28.952386+00:00
-- url     : https://prove2.me/theorems/d18b1945-ba30-48c8-b363-e2af9f377560
-- title:
--   First Passage Linear Transport: shell Bad timeout Endpoint Good
-- statement:
--   The shell complement of the canonical timeout good set is exactly the
--   separated timeout envelope.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L377-L409
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L377-L409

import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellBad_timeoutEndpointGood
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (A : ℕ → ℝ) (M : ℕ) :
    shellBad (timeoutEndpointGood P A M) M =
      timeoutSeparatedFailureEnvelope P.run.toTimeoutHigh P.K₀ M
        (movingTerminalRank A M) (shrinkingSwitchRank P.Cswitch M) := by sorry
