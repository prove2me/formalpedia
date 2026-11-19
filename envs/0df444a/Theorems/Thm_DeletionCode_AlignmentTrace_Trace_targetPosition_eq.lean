-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_targetPosition_eq
-- name    : DeletionCode.AlignmentTrace.Trace.targetPosition_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:32:16.199665+00:00
-- url     : https://prove2.me/theorems/16603037-f02d-4a36-806c-37699453a22f
-- title:
--   Trace: target Position eq
-- statement:
--   The target position is the matched anchor plus preceding insertions.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L167-L169
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L167-L169

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.targetPosition_eq (trace : Trace) (j : ℕ) :
    targetPosition trace j = matchedAnchor trace j + insertions (trace.take j) := by sorry
