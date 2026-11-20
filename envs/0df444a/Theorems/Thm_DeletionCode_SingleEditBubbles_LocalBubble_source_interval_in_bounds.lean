-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_source_interval_in_bounds
-- name    : DeletionCode.SingleEditBubbles.LocalBubble.source_interval_in_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:28.766399+00:00
-- url     : https://prove2.me/theorems/55dce5ae-00d3-4d48-9f64-6e76b5940a77
-- title:
--   Local Bubble: source interval in bounds
-- statement:
--   The Local Bubble construction uses the source interval in bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L45-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L45-L50

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
open DeletionCode.SingleEditBubbles.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.SingleEditBubbles.LocalBubble.source_interval_in_bounds (p : LocalBubble k source target pos orientation) :
    sourceInterval p ⊆ Set.Ico 0 source.length := by sorry
