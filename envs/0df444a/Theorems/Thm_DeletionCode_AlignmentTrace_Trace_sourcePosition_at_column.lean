-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_sourcePosition_at_column
-- name    : DeletionCode.AlignmentTrace.Trace.sourcePosition_at_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:10.404057+00:00
-- url     : https://prove2.me/theorems/9ea88efe-a69a-4f5a-9644-c2fb5e22dd4c
-- title:
--   Trace: source Position at column
-- statement:
--   The Trace construction uses the source Position at column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L140-L142
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L140-L142

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.sourcePosition_at_column (pre suffix : Trace) (col : Column) :
    sourcePosition (pre ++ col :: suffix) pre.length = pre.source.length := by sorry
