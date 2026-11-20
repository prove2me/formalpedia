-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_trace_of_equal_length_confusability
-- name    : DeletionCode.AlignmentTrace.trace_of_equal_length_confusability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:27:28.926193+00:00
-- url     : https://prove2.me/theorems/c9dd5d58-0083-41bf-9ab0-b7b2a7caed84
-- title:
--   Alignment Trace: trace of equal length confusability
-- statement:
--   Confusability yields actual finite alignment data with the exact counters.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L213-L220
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L213-L220

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment

theorem DeletionCode.AlignmentTrace.trace_of_equal_length_confusability (y z u : Word) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ (d : ℕ) (trace : Trace), d ≤ t ∧ trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = d := by sorry
