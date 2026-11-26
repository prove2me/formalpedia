-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_lt_source
-- name    : FirstPassageLinearTransport.eventually_shrinkingSwitchRank_lt_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:35.08548+00:00
-- url     : https://prove2.me/theorems/c510f846-81e7-5ad7-b922-c2b44bf03105
-- title:
--   First Passage Linear Transport: eventually shrinking Switch Rank lt source
-- statement:
--   A linear-log switch is eventually below the source shell.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L73-L115
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L73-L115

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_shrinkingSwitchRank_lt_source
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, shrinkingSwitchRank C M < M := by sorry
