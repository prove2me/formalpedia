-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingTimePotential_source_le_sqrt
-- name    : FirstPassageLinearTransport.shrinkingTimePotential_source_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:01.362915+00:00
-- url     : https://prove2.me/theorems/c446a81f-dcfe-4900-a35b-d60ce4a95f3e
-- title:
--   First Passage Linear Transport: shrinking Time Potential source le sqrt
-- statement:
--   Exact potential estimate for the canonical linear-log switch.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L198-L298
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L198-L298

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shrinkingTimePotential_source_le_sqrt
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C)
    {M : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M < M + 1) :
    1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap ≤
      shrinkingTimeSupportConstant P C *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
