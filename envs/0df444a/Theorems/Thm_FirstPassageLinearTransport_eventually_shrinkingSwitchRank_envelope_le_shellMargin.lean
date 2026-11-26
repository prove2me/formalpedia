-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_envelope_le_shellMargin
-- name    : FirstPassageLinearTransport.eventually_shrinkingSwitchRank_envelope_le_shellMargin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:38:20.015061+00:00
-- url     : https://prove2.me/theorems/2a1051e7-f42a-4d07-998c-024fb0524bdc
-- title:
--   First Passage Linear Transport: eventually shrinking Switch Rank envelope le shell Margin
-- statement:
--   The complete low-rank local envelope is absorbed by any fixed outer
--   power margin because the switch has only logarithmic rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L459-L504
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean#L459-L504

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_shrinkingSwitchRank_envelope_le_shellMargin
    {C eta beta : ℝ} (hC : 0 ≤ C) (heta : 0 ≤ eta)
    (hbeta : 0 < beta) :
    ∀ᶠ M : ℕ in atTop,
      (shrinkingSwitchRank C M : ℝ) * (1 + eta) ≤ beta * (M : ℝ) := by sorry
