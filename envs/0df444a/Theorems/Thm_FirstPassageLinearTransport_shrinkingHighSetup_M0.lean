-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
-- name    : FirstPassageLinearTransport.shrinkingHighSetup_M0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:33.995452+00:00
-- url     : https://prove2.me/theorems/2499c969-f041-550a-adae-3fe8e892cf0a
-- title:
--   First Passage Linear Transport: shrinking High Setup M0
-- statement:
--   The First Passage Linear Transport construction uses the shrinking High Setup M0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L83-L85
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L83-L85

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.shrinkingHighSetup_M0
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    (shrinkingHighSetup P M m).M0 = P.pHi.M0 := by sorry

attribute [defeq] FirstPassageLinearTransport.shrinkingHighSetup_M0
