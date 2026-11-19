-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_deletions_append
-- name    : DeletionCode.AlignmentTrace.Trace.deletions_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:32:09.539578+00:00
-- url     : https://prove2.me/theorems/b2f18cd1-6123-49e0-bf30-3de73ae3ce41
-- title:
--   Trace: deletions append
-- statement:
--   The Trace construction uses the deletions append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L72-L77
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L72-L77

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.deletions_append (left right : Trace) :
    deletions (left ++ right) = deletions left + deletions right := by sorry
