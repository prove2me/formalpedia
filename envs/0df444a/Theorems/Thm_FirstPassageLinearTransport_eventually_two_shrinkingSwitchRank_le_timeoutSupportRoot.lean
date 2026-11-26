-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_two_shrinkingSwitchRank_le_timeoutSupportRoot
-- name    : FirstPassageLinearTransport.eventually_two_shrinkingSwitchRank_le_timeoutSupportRoot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:12.360303+00:00
-- url     : https://prove2.me/theorems/2442fc5c-226d-54ed-9751-31061978ec94
-- title:
--   First Passage Linear Transport: eventually two shrinking Switch Rank le timeout Support Root
-- statement:
--   The switch rank itself is negligible on the trajectory-tube scale.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1060-L1090
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1060-L1090

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_two_shrinkingSwitchRank_le_timeoutSupportRoot
    (P : TimeoutHighRunData) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop,
      2 * (shrinkingSwitchRank C M : ℝ) ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
