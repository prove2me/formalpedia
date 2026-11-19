-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_insertions_append
-- name    : DeletionCode.AlignmentTrace.Trace.insertions_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:32:09.082024+00:00
-- url     : https://prove2.me/theorems/65ec7593-672d-45fa-854a-169f566ae9a1
-- title:
--   Trace: insertions append
-- statement:
--   The Trace construction uses the insertions append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L79-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L79-L84

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.insertions_append (left right : Trace) :
    insertions (left ++ right) = insertions left + insertions right := by sorry
