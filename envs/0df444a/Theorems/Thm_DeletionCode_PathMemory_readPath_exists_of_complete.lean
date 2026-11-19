-- Prove2me | Theorems.Thm_DeletionCode_PathMemory_readPath_exists_of_complete
-- name    : DeletionCode.PathMemory.readPath_exists_of_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:41.495929+00:00
-- url     : https://prove2.me/theorems/52f4bd3b-9491-4152-9c52-a6e693aee58b
-- title:
--   Path Memory: read Path exists of complete
-- statement:
--   Once all negative letters are stored, every bounded block on either side is readable.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean#L93-L108
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean#L93-L108

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory
set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows

theorem DeletionCode.PathMemory.readPath_exists_of_complete (k : ℕ) (h : Header) (s : Memory)
    (side : Bool) (start len : ℕ)
    (hknown : WindowKnown s 0 (negativeLength k h))
    (hbound : start + len ≤ pathLength k h side) :
    ∃ bits, readPath k h s side start len = some bits := by sorry
