-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_windowStart_le
-- name    : DeletionCode.SelectedWindows.windowStart_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:08:26.821794+00:00
-- url     : https://prove2.me/theorems/5cfc46e2-e216-4460-9a72-35706aee235e
-- title:
--   Selected Windows: window Start le
-- statement:
--   The Selected Windows construction uses the window Start le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L17-L18
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L17-L18

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.windowStart_le (D : ℕ) (w : Slot) : windowStart D w ≤ D := by sorry
