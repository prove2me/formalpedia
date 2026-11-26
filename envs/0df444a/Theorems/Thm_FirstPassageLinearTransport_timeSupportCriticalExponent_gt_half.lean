-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_gt_half
-- name    : FirstPassageLinearTransport.timeSupportCriticalExponent_gt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:20:33.465499+00:00
-- url     : https://prove2.me/theorems/446bdac4-0a96-5c8c-a383-c196693d6e61
-- title:
--   First Passage Linear Transport: time Support Critical Exponent gt half
-- statement:
--   The First Passage Linear Transport construction uses the time Support Critical Exponent gt half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingParameters.lean#L41-L44
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingParameters.lean#L41-L44

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeSupportCriticalExponent_gt_half :
    1 / 2 < timeSupportCriticalExponent := by sorry
