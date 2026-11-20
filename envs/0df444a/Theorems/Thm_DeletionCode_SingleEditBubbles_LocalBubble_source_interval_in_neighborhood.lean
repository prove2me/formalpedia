-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_source_interval_in_neighborhood
-- name    : DeletionCode.SingleEditBubbles.LocalBubble.source_interval_in_neighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:02.971753+00:00
-- url     : https://prove2.me/theorems/fbae49e8-ccab-403a-9f74-0833723f1964
-- title:
--   Local Bubble: source interval in neighborhood
-- statement:
--   Every local source letter lies in the paper's prescribed edit neighborhood.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L53-L63
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L53-L63

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

theorem DeletionCode.SingleEditBubbles.LocalBubble.source_interval_in_neighborhood (p : LocalBubble k source target pos orientation) :
    sourceInterval p ⊆ neighborhood (windowLength k) pos := by sorry
