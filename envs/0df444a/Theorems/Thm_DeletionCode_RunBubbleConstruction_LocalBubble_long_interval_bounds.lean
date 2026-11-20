-- Prove2me | Theorems.Thm_DeletionCode_RunBubbleConstruction_LocalBubble_long_interval_bounds
-- name    : DeletionCode.RunBubbleConstruction.LocalBubble.long_interval_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:59.736618+00:00
-- url     : https://prove2.me/theorems/81419404-7f5b-4de6-8cc8-43f41ec25a16
-- title:
--   Local Bubble: long interval bounds
-- statement:
--   The Local Bubble construction uses the long interval bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L141-L147
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L141-L147

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.RunBubbleConstruction.LocalBubble.long_interval_bounds (p : LocalBubble k source target pos orientation) :
    pos + 1 - windowLength k ≤ p.before.length ∧
      p.before.length + p.bubble.longWord.length ≤ pos + windowLength k := by sorry
