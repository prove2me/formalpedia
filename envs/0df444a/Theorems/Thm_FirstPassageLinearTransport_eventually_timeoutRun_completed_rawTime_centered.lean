-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_rawTime_centered
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_completed_rawTime_centered
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:45.939221+00:00
-- url     : https://prove2.me/theorems/45af50c8-41e0-4711-adea-c703047ab267
-- title:
--   First Passage Linear Transport: eventually timeout Run completed raw Time centered
-- statement:
--   The centered raw clock remains valid after an exact-halving completion
--   from a dyadic upper endpoint to the terminal rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L338-L434
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L338-L434

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_completed_rawTime_centered
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      L = movingTerminalRank A M →
      q ≤ shrinkingSwitchRank P.Cswitch M →
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀ L M
        (shrinkingSwitchRank P.Cswitch M) n elapsed q →
      orbit elapsed n = 2 ^ q →
      |(2 * driftGap / 3) *
          (rawTime n (elapsed + (q - L)) : ℝ) - (M : ℝ)| ≤
        timeoutCompletedRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
