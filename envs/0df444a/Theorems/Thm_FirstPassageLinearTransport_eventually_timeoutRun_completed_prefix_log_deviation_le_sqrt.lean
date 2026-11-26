-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_prefix_log_deviation_le_sqrt
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_completed_prefix_log_deviation_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:31:32.904819+00:00
-- url     : https://prove2.me/theorems/1533b132-b7af-561c-b1f1-6fafd8173bbb
-- title:
--   First Passage Linear Transport: eventually timeout Run completed prefix log deviation le sqrt
-- statement:
--   Adding at most the switch rank of final shortcut steps preserves the
--   trajectory-tube scale.  This covers the exact-halving completion used when a
--   timeout run lands at a dyadic upper endpoint.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L980-L1057
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L980-L1057

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_completed_prefix_log_deviation_le_sqrt
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q v : ℕ},
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      v ≤ shrinkingSwitchRank C M →
      ∀ j : ℕ, j ≤ elapsed + v →
        |shortcutLogDeviation n j| ≤
          2 * timeoutTimeSupportConstant P C *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
