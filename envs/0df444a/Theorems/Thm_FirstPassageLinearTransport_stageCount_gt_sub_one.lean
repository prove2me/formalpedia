-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageCount_gt_sub_one
-- name    : FirstPassageLinearTransport.stageCount_gt_sub_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:23:13.0228+00:00
-- url     : https://prove2.me/theorems/09431bd4-c552-5462-b7a8-d382ff03cb99
-- title:
--   First Passage Linear Transport: stage Count gt sub one
-- statement:
--   The First Passage Linear Transport construction uses the stage Count gt sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Scalar.lean#L80-L83
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Scalar.lean#L80-L83

import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Definitions.Def_FirstPassageLinearTransport_Scalar
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter Asymptotics
noncomputable section

theorem FirstPassageLinearTransport.stageCount_gt_sub_one {omega : ℝ} (M : ℕ) :
    omega * Real.log (M + 4) - 1 < stageCount omega M := by sorry
