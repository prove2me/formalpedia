-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_length
-- name    : DeletionCode.AlignmentTrace.Trace.source_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:42.607214+00:00
-- url     : https://prove2.me/theorems/2d3ae173-cd19-43fa-8c04-3257bb1d9f08
-- title:
--   Trace: source length
-- statement:
--   The Trace construction uses the source length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L93-L98
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L93-L98

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.source_length (trace : Trace) :
    trace.source.length = trace.matchedCount + trace.deletions := by sorry
