-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_oddCount_centered_le_sqrt
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_prefix_oddCount_centered_le_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:51:07.287691+00:00
-- url     : https://prove2.me/theorems/b1ebb27c-30d8-4de7-a623-073583adefbc
-- title:
--   First Passage Linear Transport: eventually timeout Run prefix odd Count centered le sqrt
-- statement:
--   Constant-times-root form of the run-wide odd-count profile.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1141-L1178
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1141-L1178

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_prefix_oddCount_centered_le_sqrt
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      ∀ j : ℕ, j ≤ elapsed →
        |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
          timeoutOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
