-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcut_gt_of_odd
-- name    : FirstPassageLinearTransport.shortcut_gt_of_odd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:34.190019+00:00
-- url     : https://prove2.me/theorems/f9c1b2cd-1a49-5e5b-a005-396f7007075b
-- title:
--   First Passage Linear Transport: shortcut gt of odd
-- statement:
--   The First Passage Linear Transport construction uses the shortcut gt of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L150-L152
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L150-L152

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.shortcut_gt_of_odd {x : ℕ} (hodd : x % 2 = 1) : x < shortcut x := by sorry
