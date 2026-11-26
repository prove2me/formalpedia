-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingTargetTolerance_eq_high
-- name    : FirstPassageLinearTransport.shrinkingTargetTolerance_eq_high
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:18:59.165618+00:00
-- url     : https://prove2.me/theorems/dc29a00c-4c5d-5dda-882b-9197aeeed003
-- title:
--   First Passage Linear Transport: shrinking Target Tolerance eq high
-- statement:
--   The First Passage Linear Transport construction uses the shrinking Target Tolerance eq high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L23-L28
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L23-L28

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shrinkingTargetTolerance_eq_high
    (P : ShrinkingBarrierRunData) {M S q : ℕ} (hSq : S < q) :
    shrinkingTargetTolerance P M S q =
      shrinkingHighTolerance P M (q - 1) := by sorry
