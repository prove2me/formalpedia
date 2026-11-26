-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_high_step
-- name    : FirstPassageLinearTransport.timeoutTimePotential_high_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:25:54.250214+00:00
-- url     : https://prove2.me/theorems/be3eb623-f207-5521-b956-65c5c11470b7
-- title:
--   First Passage Linear Transport: timeout Time Potential high step
-- statement:
--   One high rank drop pays its certified corridor and preserves the complete
--   future low-phase reserve.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L193-L273
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L193-L273

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutTimePotential_high_step
    (P : TimeoutHighRunData) {M S m q : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hSm : S ≤ m)
    (hq : (q : ℝ) ≤ (P.rHi : ℝ) * (m : ℝ)) :
    timeoutDurationError (timeoutHighTolerance P M m) m +
        timeoutTimePotential P M S q ≤
      timeoutTimePotential P M S (m + 1) := by sorry
