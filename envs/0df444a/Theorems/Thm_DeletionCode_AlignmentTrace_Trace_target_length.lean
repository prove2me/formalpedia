-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_target_length
-- name    : DeletionCode.AlignmentTrace.Trace.target_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:27:11.981204+00:00
-- url     : https://prove2.me/theorems/f0c4d500-edb4-43e0-83ad-31e1a0c92f87
-- title:
--   Trace: target length
-- statement:
--   The Trace construction uses the target length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L100-L105
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L100-L105

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.target_length (trace : Trace) :
    trace.target.length = trace.matchedCount + trace.insertions := by sorry
