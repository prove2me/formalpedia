-- Prove2me | Theorems.Thm_DeletionCode_TraceBubbleFamily_indexedBubbleWords_orientation
-- name    : DeletionCode.TraceBubbleFamily.indexedBubbleWords_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:20.910437+00:00
-- url     : https://prove2.me/theorems/ec6bb70a-95ae-445f-8ed6-e8a2bd3a34ee
-- title:
--   Trace Bubble Family: indexed Bubble Words orientation
-- statement:
--   The Trace Bubble Family construction uses the indexed Bubble Words orientation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean#L81-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean#L81-L87

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceBubbleFamily
set_option autoImplicit true
open DeletionCode DeletionCode.TraceBubbleFamily
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData

theorem DeletionCode.TraceBubbleFamily.indexedBubbleWords_orientation (trace : Trace) (k t : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) (i : Fin (2 * t)) :
    (indexedBubbleWords trace k t hx hsep hdel hins i).orientation =
      orientation trace (editEquiv trace t hdel hins i) := by sorry
