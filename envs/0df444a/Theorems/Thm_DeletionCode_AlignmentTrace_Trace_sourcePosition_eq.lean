-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_sourcePosition_eq
-- name    : DeletionCode.AlignmentTrace.Trace.sourcePosition_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:32:13.756455+00:00
-- url     : https://prove2.me/theorems/49a65320-ffbe-4d52-8f24-a2e8c477c9ed
-- title:
--   Trace: source Position eq
-- statement:
--   The source position is the matched anchor plus preceding deletions.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L162-L164
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L162-L164

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.sourcePosition_eq (trace : Trace) (j : ℕ) :
    sourcePosition trace j = matchedAnchor trace j + deletions (trace.take j) := by sorry
