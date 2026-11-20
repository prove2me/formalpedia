-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_localVertex_mem
-- name    : DeletionCode.LocalBubbleDisjoint.localVertex_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:44:45.478879+00:00
-- url     : https://prove2.me/theorems/f3ed2797-4d4f-4159-89f0-1f18ed57f109
-- title:
--   Local Bubble Disjoint: local Vertex mem
-- statement:
--   Every bounded actual bubble vertex belongs to the corresponding local
--   output vertex set of the canonical edit in source coordinates.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L98-L111
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L98-L111

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.localVertex_mem (p : LocalBubble k source target pos orientation) (side : Bool)
    (offset : ℕ) (hbound : offset + (windowLength k - 1) ≤ (pathWord p side).length) :
    localVertex p side offset ∈ EditLocality.localVertices (canonicalEdit p side)
      (listLetters source) p.before.length p.bubble.negativeWord.length (windowLength k) := by sorry
