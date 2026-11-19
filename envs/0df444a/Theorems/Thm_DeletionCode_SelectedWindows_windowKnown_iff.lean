-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_iff
-- name    : DeletionCode.SelectedWindows.windowKnown_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:01:09.977591+00:00
-- url     : https://prove2.me/theorems/260937b1-54d1-42e8-b7ff-fa6237959474
-- title:
--   Selected Windows: window Known iff
-- statement:
--   The Selected Windows construction uses the window Known iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L26-L36
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L26-L36

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.windowKnown_iff (s : Memory) (start len : ℕ) :
    WindowKnown s start len ↔ ∀ i, i < len → ∃ b, s (start + i) = some b := by sorry
