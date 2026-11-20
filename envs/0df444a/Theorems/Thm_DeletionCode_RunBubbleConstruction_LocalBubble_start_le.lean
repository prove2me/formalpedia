-- Prove2me | Theorems.Thm_DeletionCode_RunBubbleConstruction_LocalBubble_start_le
-- name    : DeletionCode.RunBubbleConstruction.LocalBubble.start_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:49.330005+00:00
-- url     : https://prove2.me/theorems/699e99d5-6ed2-4987-b15a-b4429af28a7c
-- title:
--   Local Bubble: start le
-- statement:
--   The Local Bubble construction uses the start le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L125-L128
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L125-L128

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.RunBubbleConstruction.LocalBubble.start_le (p : LocalBubble k source target pos orientation) :
    p.before.length ≤ pos := by sorry
