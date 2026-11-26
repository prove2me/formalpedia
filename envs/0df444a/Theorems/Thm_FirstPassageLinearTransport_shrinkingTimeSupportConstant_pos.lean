-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingTimeSupportConstant_pos
-- name    : FirstPassageLinearTransport.shrinkingTimeSupportConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:43.058506+00:00
-- url     : https://prove2.me/theorems/76273150-5655-5e51-a49c-0060828767ba
-- title:
--   First Passage Linear Transport: shrinking Time Support Constant pos
-- statement:
--   The First Passage Linear Transport construction uses the shrinking Time Support Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L165-L184
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L165-L184

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shrinkingTimeSupportConstant_pos
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C) :
    0 < shrinkingTimeSupportConstant P C := by sorry
