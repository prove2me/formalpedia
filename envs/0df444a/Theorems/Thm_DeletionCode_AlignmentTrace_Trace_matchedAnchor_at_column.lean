-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_at_column
-- name    : DeletionCode.AlignmentTrace.Trace.matchedAnchor_at_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:10.530682+00:00
-- url     : https://prove2.me/theorems/7c30620e-39bd-491e-a4dd-4649352b03e8
-- title:
--   Trace: matched Anchor at column
-- statement:
--   The Trace construction uses the matched Anchor at column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L136-L138
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L136-L138

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.matchedAnchor_at_column (pre suffix : Trace) (col : Column) :
    matchedAnchor (pre ++ col :: suffix) pre.length = pre.matchedCount := by sorry
