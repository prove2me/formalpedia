-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_rawTime_centered
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_rawTime_centered
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:30:01.924688+00:00
-- url     : https://prove2.me/theorems/ef9eca55-a7a3-47a2-a86b-77e55e472116
-- title:
--   First Passage Linear Transport: eventually timeout Run raw Time centered
-- statement:
--   The exact raw time associated with every terminal-scale timeout run has
--   the centered drift `2*driftGap/3`.  The estimate uses the same good sources
--   and introduces no additional exceptional set.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L222-L334
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L222-L334

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_rawTime_centered
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      q ≤ shrinkingSwitchRank P.Cswitch M →
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| ≤
        timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
