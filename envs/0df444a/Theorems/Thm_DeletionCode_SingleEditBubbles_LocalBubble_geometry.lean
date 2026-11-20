-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_geometry
-- name    : DeletionCode.SingleEditBubbles.LocalBubble.geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:59.836256+00:00
-- url     : https://prove2.me/theorems/d8f3e769-4a6b-42e2-a919-f9a6a4366ccc
-- title:
--   Local Bubble: geometry
-- statement:
--   The Local Bubble construction uses the geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L20-L25
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L20-L25

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry

set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
open DeletionCode.SingleEditBubbles.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.SingleEditBubbles.LocalBubble.geometry (p : LocalBubble k source target pos orientation) (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k) : Geometry p.bubble := by sorry
