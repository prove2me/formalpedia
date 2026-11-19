-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedCount_append
-- name    : DeletionCode.AlignmentTrace.Trace.matchedCount_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:04:31.27632+00:00
-- url     : https://prove2.me/theorems/825a847f-e684-48aa-9d7c-a93a0d7fb2ed
-- title:
--   Trace: matched Count append
-- statement:
--   The Trace construction uses the matched Count append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L86-L91
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L86-L91

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.matchedCount_append (left right : Trace) :
    matchedCount (left ++ right) = matchedCount left + matchedCount right := by sorry
