-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_targetPosition_at_column
-- name    : DeletionCode.AlignmentTrace.Trace.targetPosition_at_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:15.494345+00:00
-- url     : https://prove2.me/theorems/eff57045-9296-486d-9f57-94c9a40f1399
-- title:
--   Trace: target Position at column
-- statement:
--   The Trace construction uses the target Position at column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L144-L146
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L144-L146

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.targetPosition_at_column (pre suffix : Trace) (col : Column) :
    targetPosition (pre ++ col :: suffix) pre.length = pre.target.length := by sorry
