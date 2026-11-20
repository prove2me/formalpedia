-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_alignment_iff_exists_trace
-- name    : DeletionCode.AlignmentTrace.alignment_iff_exists_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:13.145028+00:00
-- url     : https://prove2.me/theorems/b10129b4-19b1-42d7-9660-258efa2036ef
-- title:
--   Alignment Trace: alignment iff exists trace
-- statement:
--   Exact equivalence with the already verified alignment proposition.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L203-L210
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L203-L210

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment

theorem DeletionCode.AlignmentTrace.alignment_iff_exists_trace (y z : Word) (d i : ℕ) :
    Alignment y z d i ↔
      ∃ trace : Trace, trace.source = y ∧ trace.target = z ∧
        trace.deletions = d ∧ trace.insertions = i := by sorry
