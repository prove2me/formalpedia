-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_selected_window_cover
-- name    : DeletionCode.SelectedWindows.selected_window_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:03:38.282945+00:00
-- url     : https://prove2.me/theorems/29a88300-2ce1-41c6-8144-4db3a6f5e89b
-- title:
--   Selected Windows: selected window cover
-- statement:
--   Every in-bounds k-stretch lies in one of the actual selected slots.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L87-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L87-L97

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.selected_window_cover (D k a : ℕ) (hD : D < 3 * (k + 1))
    (ha : a + k ≤ 3 * (k + 1) + D) :
    ∃ w : Slot, windowStart D w ≤ a ∧ a + k ≤ windowStart D w + 3 * (k + 1) := by sorry
