-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutDurationError_high_le
-- name    : FirstPassageLinearTransport.timeoutDurationError_high_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:37.344253+00:00
-- url     : https://prove2.me/theorems/6c7a21ba-175b-4903-8434-72dfa8c77f1e
-- title:
--   First Passage Linear Transport: timeout Duration Error high le
-- statement:
--   The shrinking high corridor for the reduced high-data package.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L50-L107
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L50-L107

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutDurationError_high_le
    (P : TimeoutHighRunData) {M m : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) :
    timeoutDurationError (timeoutHighTolerance P M m) m ≤
      (P.D + P.tau + 3) *
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by sorry
