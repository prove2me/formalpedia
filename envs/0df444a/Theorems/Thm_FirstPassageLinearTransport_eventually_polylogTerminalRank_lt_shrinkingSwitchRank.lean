-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_polylogTerminalRank_lt_shrinkingSwitchRank
-- name    : FirstPassageLinearTransport.eventually_polylogTerminalRank_lt_shrinkingSwitchRank
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:19:23.61188+00:00
-- url     : https://prove2.me/theorems/cc08c7ca-2a2c-4dc5-9f5b-36f98f31d8eb
-- title:
--   First Passage Linear Transport: eventually polylog Terminal Rank lt shrinking Switch Rank
-- statement:
--   The terminal schedule lies below the linear-log switch exactly when the
--   switch coefficient strictly exceeds `A / log 2`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L119-L156
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L119-L156

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_polylogTerminalRank_lt_shrinkingSwitchRank
    {A C : ℝ} (hA : 0 ≤ A)
    (hAC : A / Real.log 2 < C) :
    ∀ᶠ M : ℕ in atTop,
      polylogTerminalRank A M < shrinkingSwitchRank C M := by sorry
