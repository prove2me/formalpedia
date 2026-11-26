-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_raw_log_deviation_le_sqrt
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_completed_raw_log_deviation_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:25.402661+00:00
-- url     : https://prove2.me/theorems/cac97e57-57df-4d0f-ac24-f49d89cc7d99
-- title:
--   First Passage Linear Transport: eventually timeout Run completed raw log deviation le sqrt
-- statement:
--   Every raw state through the selected completion witness lies in the raw
--   trajectory tube on the same timeout-good set.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1306-L1353
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1306-L1353

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_completed_raw_log_deviation_le_sqrt
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q v : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      orbit elapsed n = 2 ^ q →
      v ≤ q → v ≤ shrinkingSwitchRank P.Cswitch M →
      ∀ i : ℕ, i ≤ rawTime n (elapsed + v) →
        |rawLogDeviation n i| ≤
          timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
