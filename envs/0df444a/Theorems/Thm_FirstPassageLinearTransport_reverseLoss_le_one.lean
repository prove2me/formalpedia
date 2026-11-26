-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseLoss_le_one
-- name    : FirstPassageLinearTransport.reverseLoss_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:54.245808+00:00
-- url     : https://prove2.me/theorems/ba5110e3-6d17-4918-ac7f-16549eb93ef2
-- title:
--   First Passage Linear Transport: reverse Loss le one
-- statement:
--   The First Passage Linear Transport construction uses the reverse Loss le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L168-L176
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L168-L176

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverseLoss_le_one {n : ℕ} (hn : 0 < n) (i : ℕ) :
    reverseLoss n i ≤ 1 := by sorry
