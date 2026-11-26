-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_elapsed_add_switch_lt_shellClock
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_elapsed_add_switch_lt_shellClock
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:30:33.339004+00:00
-- url     : https://prove2.me/theorems/48b51961-7558-44a3-b985-fb8c61f3a7cb
-- title:
--   First Passage Linear Transport: eventually timeout Run elapsed add switch lt shell Clock
-- statement:
--   The timeout clock leaves enough of the strict clock margin to pay every
--   possible exact-halving completion below the logarithmic switch.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L453-L589
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L453-L589

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_elapsed_add_switch_lt_shellClock
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀ L M
        (shrinkingSwitchRank P.Cswitch M) n elapsed q →
      ((elapsed + shrinkingSwitchRank P.Cswitch M : ℕ) : ℝ) <
        c * (M : ℝ) * Real.log 2 := by sorry
