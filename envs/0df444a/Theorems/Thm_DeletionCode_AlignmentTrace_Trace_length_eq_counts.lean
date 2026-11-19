-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_length_eq_counts
-- name    : DeletionCode.AlignmentTrace.Trace.length_eq_counts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:34:05.625968+00:00
-- url     : https://prove2.me/theorems/9703ffee-9fea-43e2-b070-bd8265b9e8f2
-- title:
--   Trace: length eq counts
-- statement:
--   The Trace construction uses the length eq counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L107-L113
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L107-L113

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.length_eq_counts (trace : Trace) :
    trace.length = trace.matchedCount + trace.deletions + trace.insertions := by sorry
