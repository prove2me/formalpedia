-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingFeasibleTimes_card_le_potential
-- name    : FirstPassageLinearTransport.shrinkingFeasibleTimes_card_le_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:16.884832+00:00
-- url     : https://prove2.me/theorems/1e877a8e-bf7f-486f-a465-f2657b372f73
-- title:
--   First Passage Linear Transport: shrinking Feasible Times card le potential
-- statement:
--   Exact support-cardinality bound before asymptotic simplification.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L433-L488
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L433-L488

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.shrinkingFeasibleTimes_card_le_potential
    (P : ShrinkingBarrierRunData) {M S q : ℕ} (hM : 1 ≤ M) :
    (shrinkingFeasibleTimes P M S q).card ≤
      ⌈(1 + 2 * shrinkingTimePotential P M S (M + 1) / driftGap)⌉₊ := by sorry
