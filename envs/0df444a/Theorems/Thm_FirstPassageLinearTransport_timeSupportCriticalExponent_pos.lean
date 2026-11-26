-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_pos
-- name    : FirstPassageLinearTransport.timeSupportCriticalExponent_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:15:32.154218+00:00
-- url     : https://prove2.me/theorems/31f921e4-cf89-5cde-88c4-3827842f601f
-- title:
--   First Passage Linear Transport: time Support Critical Exponent pos
-- statement:
--   The First Passage Linear Transport construction uses the time Support Critical Exponent pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingParameters.lean#L46-L49
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingParameters.lean#L46-L49

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeSupportCriticalExponent_pos :
    0 < timeSupportCriticalExponent := by sorry
