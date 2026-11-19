-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_append
-- name    : DeletionCode.AlignmentTrace.Trace.source_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:26:55.829985+00:00
-- url     : https://prove2.me/theorems/ad74ee1f-5483-461d-9705-a017637b4d8b
-- title:
--   Trace: source append
-- statement:
--   The Trace construction uses the source append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L60-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L60-L64

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.source_append (left right : Trace) :
    source (left ++ right) = source left ++ source right := by sorry
