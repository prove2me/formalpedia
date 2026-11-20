-- Prove2me | Theorems.Thm_DeletionCode_TraceBubbleFamily_bubbleAt_source
-- name    : DeletionCode.TraceBubbleFamily.bubbleAt_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:25.36818+00:00
-- url     : https://prove2.me/theorems/81127973-77ab-4bc6-8cf2-31e1d3c36a51
-- title:
--   Trace Bubble Family: bubble At source
-- statement:
--   The Trace Bubble Family construction uses the bubble At source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean#L54-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean#L54-L59

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceBubbleFamily
set_option autoImplicit true
open DeletionCode DeletionCode.TraceBubbleFamily
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData

theorem DeletionCode.TraceBubbleFamily.bubbleAt_source (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    trace.source = (bubbleAt trace k hx hsep c).before ++
      (bubbleAt trace k hx hsep c).bubble.negativeWord ++ (bubbleAt trace k hx hsep c).after := by sorry
