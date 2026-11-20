-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_canonical_word
-- name    : DeletionCode.LocalBubbleDisjoint.canonical_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:45:20.455224+00:00
-- url     : https://prove2.me/theorems/7a972e87-2c65-4295-a116-7d878ba89c09
-- title:
--   Local Bubble Disjoint: canonical word
-- statement:
--   The whole output word is reconstructed from the canonical edit and
--   the actual source decomposition. No supplied substring realization is used.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L73-L94
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L73-L94

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.canonical_word (p : LocalBubble k source target pos orientation) (side : Bool) :
    (canonicalEdit p side).word (listLetters source) =
      listLetters (p.before ++ (pathWord p side ++ p.after)) := by sorry
