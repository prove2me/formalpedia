-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_canonical_valid
-- name    : DeletionCode.LocalBubbleDisjoint.canonical_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:45:18.27124+00:00
-- url     : https://prove2.me/theorems/d7ac945c-44e0-4725-9b20-241c29b89bb4
-- title:
--   Local Bubble Disjoint: canonical valid
-- statement:
--   The Local Bubble Disjoint construction uses the canonical valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L54-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L54-L59

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.canonical_valid (p : LocalBubble k source target pos orientation) (side : Bool) :
    (canonicalEdit p side).Valid source.length := by sorry
