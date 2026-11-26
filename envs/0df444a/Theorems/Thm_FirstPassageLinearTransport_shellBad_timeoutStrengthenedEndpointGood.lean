-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellBad_timeoutStrengthenedEndpointGood
-- name    : FirstPassageLinearTransport.shellBad_timeoutStrengthenedEndpointGood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:31.020803+00:00
-- url     : https://prove2.me/theorems/0e633aaa-643a-52b1-9908-3b126f5cd802
-- title:
--   First Passage Linear Transport: shell Bad timeout Strengthened Endpoint Good
-- statement:
--   The shell complement of the strengthened good set is exactly the joint
--   timeout-and-height envelope.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L413-L458
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean#L413-L458

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

theorem FirstPassageLinearTransport.shellBad_timeoutStrengthenedEndpointGood
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (A R : ℕ → ℝ) (M : ℕ) :
    shellBad (timeoutStrengthenedEndpointGood P A R M) M =
      timeoutStrengthenedFailureEnvelope P.run.toTimeoutHigh P.K₀ M
        (movingTerminalRank A M) (shrinkingSwitchRank P.Cswitch M) (R M) := by sorry
