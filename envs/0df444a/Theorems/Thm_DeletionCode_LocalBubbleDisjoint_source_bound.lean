-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_source_bound
-- name    : DeletionCode.LocalBubbleDisjoint.source_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:45:09.59908+00:00
-- url     : https://prove2.me/theorems/8a2f6788-eadc-40ed-9551-54c37a5022ea
-- title:
--   Local Bubble Disjoint: source bound
-- statement:
--   The Local Bubble Disjoint construction uses the source bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L39-L43
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L39-L43

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.source_bound (p : LocalBubble k source target pos orientation) :
    p.before.length + p.bubble.negativeWord.length ≤ source.length := by sorry
