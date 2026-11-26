-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassage_odd_following_gt
-- name    : FirstPassageLinearTransport.firstPassage_odd_following_gt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:38.227373+00:00
-- url     : https://prove2.me/theorems/28b56701-3c83-43ad-93bb-2eedeb3910bd
-- title:
--   First Passage Linear Transport: first Passage odd following gt
-- statement:
--   The First Passage Linear Transport construction uses the first Passage odd following gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L154-L161
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L154-L161

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.firstPassage_odd_following_gt {Y n h i : ℕ}
    (hfp : IsFirstPassage Y n h) (hi : i < h)
    (hodd : (parityBit n i : ℕ) = 1) :
    Y < orbit (i + 1) n := by sorry
