-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_raw_log_deviation_le_sqrt
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_prefix_raw_log_deviation_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:50:32.988917+00:00
-- url     : https://prove2.me/theorems/47821e58-4e13-5ac2-8bb2-f97afd714c83
-- title:
--   First Passage Linear Transport: eventually timeout Run prefix raw log deviation le sqrt
-- statement:
--   Every raw prefix of a moving-endpoint timeout run lies in a uniform
--   `sqrt(M log M)` tube on exactly the same good set.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1357-L1418
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1357-L1418

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_prefix_raw_log_deviation_le_sqrt
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      ∀ i : ℕ, i ≤ rawTime n elapsed →
        |rawLogDeviation n i| ≤
          timeoutRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
