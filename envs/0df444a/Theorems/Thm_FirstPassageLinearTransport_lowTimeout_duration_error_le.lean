-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lowTimeout_duration_error_le
-- name    : FirstPassageLinearTransport.lowTimeout_duration_error_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:47.830234+00:00
-- url     : https://prove2.me/theorems/456f7164-4d92-4922-b436-f627696c2c93
-- title:
--   First Passage Linear Transport: low Timeout duration error le
-- statement:
--   A timeout block has corridor width at most the switch rank.  This uses
--   only `duration ≤ m`, `q < m`, and `m < S`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L111-L140
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L111-L140

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.lowTimeout_duration_error_le
    {K₀ : ℝ} {L S m x : ℕ}
    (hmS : m < S) (hpass : LowTimeoutPassage K₀ L m x)
    (hqparent : timeoutTargetRank K₀ L m < m) :
    |driftGap * (hpass.duration : ℝ) -
        ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1 ≤ S := by sorry
