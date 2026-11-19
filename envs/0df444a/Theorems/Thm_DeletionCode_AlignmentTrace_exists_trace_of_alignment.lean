-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_exists_trace_of_alignment
-- name    : DeletionCode.AlignmentTrace.exists_trace_of_alignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:51.473213+00:00
-- url     : https://prove2.me/theorems/73c0fc73-01c2-44b1-8452-2601f99af50d
-- title:
--   Alignment Trace: exists trace of alignment
-- statement:
--   Propositional alignability has an explicit trace witness. Different
--   traces can remain distinct data even when their word projections agree.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L183-L200
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L183-L200

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment

theorem DeletionCode.AlignmentTrace.exists_trace_of_alignment {y z : Word} {d i : ℕ}
    (h : Alignment y z d i) :
    ∃ trace : Trace, trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = i := by sorry
