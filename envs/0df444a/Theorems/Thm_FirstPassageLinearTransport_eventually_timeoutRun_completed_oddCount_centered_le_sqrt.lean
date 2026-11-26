-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_oddCount_centered_le_sqrt
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_completed_oddCount_centered_le_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:33:26.700362+00:00
-- url     : https://prove2.me/theorems/a6916416-138d-47a1-ae0a-efc4402a9b32
-- title:
--   First Passage Linear Transport: eventually timeout Run completed odd Count centered le sqrt
-- statement:
--   The odd-count tube persists through the exact-halving completion used by
--   the selected endpoint witness.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1204-L1271
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1204-L1271

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_completed_oddCount_centered_le_sqrt
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
      ∀ j : ℕ, j ≤ elapsed + v →
        |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
          timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
