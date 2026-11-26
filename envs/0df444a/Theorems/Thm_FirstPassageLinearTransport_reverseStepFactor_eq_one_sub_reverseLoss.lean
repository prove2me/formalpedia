-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseStepFactor_eq_one_sub_reverseLoss
-- name    : FirstPassageLinearTransport.reverseStepFactor_eq_one_sub_reverseLoss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:34.45211+00:00
-- url     : https://prove2.me/theorems/3ee1c840-2aaa-552d-a9ca-c42bca54ee26
-- title:
--   First Passage Linear Transport: reverse Step Factor eq one sub reverse Loss
-- statement:
--   The First Passage Linear Transport construction uses the reverse Step Factor eq one sub reverse Loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L139-L143
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L139-L143

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverseStepFactor_eq_one_sub_reverseLoss (n i : ℕ) :
    reverseStepFactor n i = 1 - reverseLoss n i := by sorry
