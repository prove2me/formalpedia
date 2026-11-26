-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_lt_a0
-- name    : FirstPassageLinearTransport.shrinkingHighTolerance_lt_a0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:19.255716+00:00
-- url     : https://prove2.me/theorems/b5c68121-2312-4cf1-acbd-3e1555e06ac1
-- title:
--   First Passage Linear Transport: shrinking High Tolerance lt a0
-- statement:
--   The First Passage Linear Transport construction uses the shrinking High Tolerance lt a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L70-L73
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L70-L73

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.shrinkingHighTolerance_lt_a0
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    shrinkingHighTolerance P M m < a0 := by sorry
