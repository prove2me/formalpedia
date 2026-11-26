-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_StageSetup_M0_pos
-- name    : FirstPassageLinearTransport.StageSetup.M0_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:05.549814+00:00
-- url     : https://prove2.me/theorems/1e2944a0-f618-47ca-88e0-c8c031c7b215
-- title:
--   Stage Setup: M0 pos
-- statement:
--   Every usable stage package starts at a positive shell rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L55-L61
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L55-L61

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.StageSetup.M0_pos {r eta : ℝ} (p : StageSetup r eta) :
    1 ≤ p.M0 := by sorry
