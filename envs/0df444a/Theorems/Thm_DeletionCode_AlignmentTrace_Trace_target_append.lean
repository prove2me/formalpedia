-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_target_append
-- name    : DeletionCode.AlignmentTrace.Trace.target_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:27:14.580853+00:00
-- url     : https://prove2.me/theorems/32860531-b1b8-4074-84a9-f7fe6da4b82f
-- title:
--   Trace: target append
-- statement:
--   The Trace construction uses the target append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L66-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L66-L70

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.target_append (left right : Trace) :
    target (left ++ right) = target left ++ target right := by sorry
