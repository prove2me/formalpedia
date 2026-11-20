-- Prove2me | Theorems.Thm_DeletionCode_TraceBubbleFamily_bubbleAt_orientation
-- name    : DeletionCode.TraceBubbleFamily.bubbleAt_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:11.567056+00:00
-- url     : https://prove2.me/theorems/3728a295-60f1-4ca7-9b8f-c54de53f219f
-- title:
--   Trace Bubble Family: bubble At orientation
-- statement:
--   The Trace Bubble Family construction uses the bubble At orientation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean#L48-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean#L48-L52

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceBubbleFamily
set_option autoImplicit true
open DeletionCode DeletionCode.TraceBubbleFamily
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData

theorem DeletionCode.TraceBubbleFamily.bubbleAt_orientation (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    (bubbleAt trace k hx hsep c).bubble.orientation = orientation trace c := by sorry
