-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_alignment
-- name    : DeletionCode.AlignmentTrace.Trace.alignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:27:12.776033+00:00
-- url     : https://prove2.me/theorems/b2336f47-f76f-46cf-98fc-53436fff280c
-- title:
--   Trace: alignment
-- statement:
--   Every computational trace is a genuine alignment of its projections.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L116-L124
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L116-L124

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.alignment (trace : Trace) :
    Alignment trace.source trace.target trace.deletions trace.insertions := by sorry
