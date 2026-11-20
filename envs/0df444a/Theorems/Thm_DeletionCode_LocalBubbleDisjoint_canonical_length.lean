-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_canonical_length
-- name    : DeletionCode.LocalBubbleDisjoint.canonical_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:45:41.526237+00:00
-- url     : https://prove2.me/theorems/a18b0e8d-112b-483e-b64b-878250ddf344
-- title:
--   Local Bubble Disjoint: canonical length
-- statement:
--   The Local Bubble Disjoint construction uses the canonical length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L61-L69
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L61-L69

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.canonical_length (p : LocalBubble k source target pos orientation) (side : Bool) :
    (pathWord p side).length = (canonicalEdit p side).outputLength p.bubble.negativeWord.length := by sorry
