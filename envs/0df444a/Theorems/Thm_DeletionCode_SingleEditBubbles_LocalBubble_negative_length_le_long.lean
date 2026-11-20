-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_negative_length_le_long
-- name    : DeletionCode.SingleEditBubbles.LocalBubble.negative_length_le_long
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:19.844451+00:00
-- url     : https://prove2.me/theorems/cf5d0fbb-3287-4d28-911e-c7ce45840dbc
-- title:
--   Local Bubble: negative length le long
-- statement:
--   The Local Bubble construction uses the negative length le long property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L40-L43
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L40-L43

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

theorem DeletionCode.SingleEditBubbles.LocalBubble.negative_length_le_long (p : LocalBubble k source target pos orientation) :
    p.bubble.negativeWord.length ≤ p.bubble.longWord.length := by sorry
