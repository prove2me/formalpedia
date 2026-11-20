-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_vertices_subset
-- name    : DeletionCode.LocalBubbleDisjoint.vertices_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:45:16.645958+00:00
-- url     : https://prove2.me/theorems/1aa67017-ad5b-4f2f-835c-f7ec6158c6e1
-- title:
--   Local Bubble Disjoint: vertices subset
-- statement:
--   The Local Bubble Disjoint construction uses the vertices subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L113-L117
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L113-L117

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.vertices_subset (p : LocalBubble k source target pos orientation) (side : Bool) :
    vertices p side ⊆ EditLocality.localVertices (canonicalEdit p side)
      (listLetters source) p.before.length p.bubble.negativeWord.length (windowLength k) := by sorry
