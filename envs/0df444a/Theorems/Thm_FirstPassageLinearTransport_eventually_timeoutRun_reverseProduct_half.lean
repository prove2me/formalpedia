-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_reverseProduct_half
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_reverseProduct_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:29:48.804918+00:00
-- url     : https://prove2.me/theorems/08715179-91a0-5071-9144-fb14939c4751
-- title:
--   First Passage Linear Transport: eventually timeout Run reverse Product half
-- statement:
--   Eventually every timeout run in the moving endpoint construction has a
--   reverse product bounded below by one half.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L116-L176
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L116-L176

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_reverseProduct_half
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      (1 / 2 : ℚ) ≤ reverseProduct n elapsed := by sorry
