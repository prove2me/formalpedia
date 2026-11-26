-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseLoss_le_firstPassage
-- name    : FirstPassageLinearTransport.reverseLoss_le_firstPassage
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:48.621395+00:00
-- url     : https://prove2.me/theorems/44150c60-cec2-4d6a-8510-cdb69f06cd81
-- title:
--   First Passage Linear Transport: reverse Loss le first Passage
-- statement:
--   The First Passage Linear Transport construction uses the reverse Loss le first Passage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L178-L189
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L178-L189

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverseLoss_le_firstPassage {Y n h i : ℕ}
    (hY : 0 < Y) (hfp : IsFirstPassage Y n h) (hi : i < h) :
    reverseLoss n i ≤ 1 / (2 * (Y : ℚ)) := by sorry
