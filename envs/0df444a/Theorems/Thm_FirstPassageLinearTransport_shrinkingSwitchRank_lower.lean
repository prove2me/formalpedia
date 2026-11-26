-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lower
-- name    : FirstPassageLinearTransport.shrinkingSwitchRank_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:02.674266+00:00
-- url     : https://prove2.me/theorems/eb572edd-9df4-4213-9979-7c360257026c
-- title:
--   First Passage Linear Transport: shrinking Switch Rank lower
-- statement:
--   The First Passage Linear Transport construction uses the shrinking Switch Rank lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L30-L32
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L30-L32

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shrinkingSwitchRank_lower (C : ℝ) (M : ℕ) :
    C * Real.log ((M : ℝ) + 2) ≤ (shrinkingSwitchRank C M : ℝ) := by sorry
