-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_pos
-- name    : FirstPassageLinearTransport.shrinkingSwitchRank_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:18:41.763475+00:00
-- url     : https://prove2.me/theorems/ab07fd8d-f810-5989-9950-10dec276ee62
-- title:
--   First Passage Linear Transport: shrinking Switch Rank pos
-- statement:
--   The First Passage Linear Transport construction uses the shrinking Switch Rank pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L44-L51
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L44-L51

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shrinkingSwitchRank_pos
    {C : ℝ} (hC : 0 < C) (M : ℕ) :
    0 < shrinkingSwitchRank C M := by sorry
