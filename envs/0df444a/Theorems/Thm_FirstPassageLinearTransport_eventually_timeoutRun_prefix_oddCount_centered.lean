-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_oddCount_centered
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_prefix_oddCount_centered
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:27:54.850194+00:00
-- url     : https://prove2.me/theorems/375f6bf1-44ba-5396-b39d-57402c18a098
-- title:
--   First Passage Linear Transport: eventually timeout Run prefix odd Count centered
-- statement:
--   On the moving-endpoint good route, the same prefix set also has a
--   centered odd-count profile.  No additional exceptional event is introduced:
--   the final reverse-product lower bound propagates backwards to every prefix.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1095-L1124
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1095-L1124

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_prefix_oddCount_centered
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
          (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) +
            Real.log 2) / Real.log 3 := by sorry
