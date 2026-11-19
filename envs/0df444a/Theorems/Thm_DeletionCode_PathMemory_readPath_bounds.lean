-- Prove2me | Theorems.Thm_DeletionCode_PathMemory_readPath_bounds
-- name    : DeletionCode.PathMemory.readPath_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:32.959658+00:00
-- url     : https://prove2.me/theorems/3de64a85-1086-4a28-bf43-03d88903b521
-- title:
--   Path Memory: read Path bounds
-- statement:
--   The Path Memory construction uses the read Path bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean#L39-L53
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean#L39-L53

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory
set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows

theorem DeletionCode.PathMemory.readPath_bounds (k : ℕ) (h : Header) (s : Memory) (side : Bool)
    (start len : ℕ) (bits : PartialWords.Bits len)
    (hread : readPath k h s side start len = some bits) :
    start + len ≤ pathLength k h side := by sorry
