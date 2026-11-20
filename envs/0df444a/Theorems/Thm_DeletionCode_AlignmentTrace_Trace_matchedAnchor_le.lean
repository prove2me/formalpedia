-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_le
-- name    : DeletionCode.AlignmentTrace.Trace.matchedAnchor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:45:29.861168+00:00
-- url     : https://prove2.me/theorems/f6ec4d3b-1ff3-4617-a14f-0e04f2549e23
-- title:
--   Trace: matched Anchor le
-- statement:
--   The Trace construction uses the matched Anchor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L154-L159
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L154-L159

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.matchedAnchor_le (trace : Trace) (j : ℕ) :
    matchedAnchor trace j ≤ trace.matchedCount := by sorry
