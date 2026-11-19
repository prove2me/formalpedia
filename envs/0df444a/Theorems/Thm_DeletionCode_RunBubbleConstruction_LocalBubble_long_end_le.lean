-- Prove2me | Theorems.Thm_DeletionCode_RunBubbleConstruction_LocalBubble_long_end_le
-- name    : DeletionCode.RunBubbleConstruction.LocalBubble.long_end_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:33:08.899613+00:00
-- url     : https://prove2.me/theorems/2798c857-9353-46c8-8590-18127b55370a
-- title:
--   Local Bubble: long end le
-- statement:
--   The entire longer local word ends at most L positions after the edit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L131-L139
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L131-L139

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.RunBubbleConstruction.LocalBubble.long_end_le (p : LocalBubble k source target pos orientation) :
    p.before.length + p.bubble.longWord.length ≤ pos + windowLength k := by sorry
