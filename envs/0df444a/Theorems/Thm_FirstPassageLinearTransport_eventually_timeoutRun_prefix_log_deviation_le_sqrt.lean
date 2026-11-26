-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_prefix_log_deviation_le_sqrt
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_prefix_log_deviation_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:27:52.390801+00:00
-- url     : https://prove2.me/theorems/1f83c9f2-c18c-5e62-b5d0-d7b713c8a5b1
-- title:
--   First Passage Linear Transport: eventually timeout Run prefix log deviation le sqrt
-- statement:
--   The run-wide shortcut tube has the same
--   `sqrt(M log M)` scale as the feasible-time support.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L939-L975
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L939-L975

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_prefix_log_deviation_le_sqrt
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      ∀ j : ℕ, j ≤ elapsed →
        |shortcutLogDeviation n j| ≤
          timeoutTimeSupportConstant P C *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
