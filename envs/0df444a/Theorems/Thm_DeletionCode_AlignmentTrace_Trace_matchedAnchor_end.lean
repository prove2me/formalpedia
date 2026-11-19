-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
-- name    : DeletionCode.AlignmentTrace.Trace.matchedAnchor_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:49.547603+00:00
-- url     : https://prove2.me/theorems/62edc49e-a02f-47e9-a109-2fb9f0600bc3
-- title:
--   Trace: matched Anchor end
-- statement:
--   The Trace construction uses the matched Anchor end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L150-L152
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L150-L152

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.matchedAnchor_end (trace : Trace) :
    matchedAnchor trace trace.length = trace.matchedCount := by sorry
