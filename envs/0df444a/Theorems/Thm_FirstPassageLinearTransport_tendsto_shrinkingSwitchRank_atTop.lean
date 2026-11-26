-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_shrinkingSwitchRank_atTop
-- name    : FirstPassageLinearTransport.tendsto_shrinkingSwitchRank_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:42.52585+00:00
-- url     : https://prove2.me/theorems/b7c46589-e1aa-402d-a995-dd1e7c01b044
-- title:
--   First Passage Linear Transport: tendsto shrinking Switch Rank at Top
-- statement:
--   A positive linear-logarithmic switch rank tends to infinity.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L54-L69
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L54-L69

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_shrinkingSwitchRank_atTop
    {C : ℝ} (hC : 0 < C) :
    Tendsto (shrinkingSwitchRank C) atTop atTop := by sorry
