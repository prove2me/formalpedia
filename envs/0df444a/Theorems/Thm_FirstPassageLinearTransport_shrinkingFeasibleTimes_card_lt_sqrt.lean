-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingFeasibleTimes_card_lt_sqrt
-- name    : FirstPassageLinearTransport.shrinkingFeasibleTimes_card_lt_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:49:55.157592+00:00
-- url     : https://prove2.me/theorems/0f7a55d5-8281-5c9b-bd93-783183fba6ae
-- title:
--   First Passage Linear Transport: shrinking Feasible Times card lt sqrt
-- statement:
--   Canonical feasible-time sets have square-root-logarithmic cardinality.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L301-L367
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L301-L367

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shrinkingFeasibleTimes_card_lt_sqrt
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C)
    {M q : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M < M + 1) :
    ((shrinkingFeasibleTimes P M (shrinkingSwitchRank C M) q).card : ℝ) <
      (shrinkingTimeSupportConstant P C + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
