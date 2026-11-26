-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lt_add_one
-- name    : FirstPassageLinearTransport.shrinkingSwitchRank_lt_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:28.789911+00:00
-- url     : https://prove2.me/theorems/5bb18ddd-1d8c-5814-a014-be4e0eb9193c
-- title:
--   First Passage Linear Transport: shrinking Switch Rank lt add one
-- statement:
--   The First Passage Linear Transport construction uses the shrinking Switch Rank lt add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L34-L42
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L34-L42

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shrinkingSwitchRank_lt_add_one
    {C : ℝ} (hC : 0 ≤ C) (M : ℕ) :
    (shrinkingSwitchRank C M : ℝ) <
      C * Real.log ((M : ℝ) + 2) + 1 := by sorry
