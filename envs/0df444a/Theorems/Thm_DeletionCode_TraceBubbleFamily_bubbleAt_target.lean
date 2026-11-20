-- Prove2me | Theorems.Thm_DeletionCode_TraceBubbleFamily_bubbleAt_target
-- name    : DeletionCode.TraceBubbleFamily.bubbleAt_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:26.420189+00:00
-- url     : https://prove2.me/theorems/31929016-7dfc-431d-9d3b-0e5bd2ff6dc9
-- title:
--   Trace Bubble Family: bubble At target
-- statement:
--   The Trace Bubble Family construction uses the bubble At target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean#L61-L66
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceBubbleFamily.lean#L61-L66

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceBubbleFamily
set_option autoImplicit true
open DeletionCode DeletionCode.TraceBubbleFamily
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData

theorem DeletionCode.TraceBubbleFamily.bubbleAt_target (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    oneEditTarget trace c = (bubbleAt trace k hx hsep c).before ++
      (bubbleAt trace k hx hsep c).bubble.positiveWord ++ (bubbleAt trace k hx hsep c).after := by sorry
