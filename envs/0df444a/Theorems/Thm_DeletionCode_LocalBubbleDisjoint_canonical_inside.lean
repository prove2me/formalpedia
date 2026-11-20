-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_canonical_inside
-- name    : DeletionCode.LocalBubbleDisjoint.canonical_inside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:45:10.306246+00:00
-- url     : https://prove2.me/theorems/cf5fd8d4-5fa8-4ef2-9c60-5cd4b705d4ef
-- title:
--   Local Bubble Disjoint: canonical inside
-- statement:
--   The Local Bubble Disjoint construction uses the canonical inside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L45-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L45-L52

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.canonical_inside (p : LocalBubble k source target pos orientation) (side : Bool) :
    EditLocality.Inside (canonicalEdit p side) p.before.length p.bubble.negativeWord.length := by sorry
