-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingTargetTolerance_eq_low
-- name    : FirstPassageLinearTransport.shrinkingTargetTolerance_eq_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:49.030295+00:00
-- url     : https://prove2.me/theorems/1f57e85d-d7eb-4997-8279-8d8617aed708
-- title:
--   First Passage Linear Transport: shrinking Target Tolerance eq low
-- statement:
--   The First Passage Linear Transport construction uses the shrinking Target Tolerance eq low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L30-L35
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L30-L35

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shrinkingTargetTolerance_eq_low
    (P : ShrinkingBarrierRunData) {M S q : ℕ}
    (hq1 : 1 ≤ q) (hqS : q ≤ S) :
    shrinkingTargetTolerance P M S q = P.etaLo := by sorry
