-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end_eq_sub
-- name    : DeletionCode.AlignmentTrace.Trace.matchedAnchor_end_eq_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:13.767238+00:00
-- url     : https://prove2.me/theorems/bb35b0d9-efa5-4568-9828-ad0ae40957e3
-- title:
--   Trace: matched Anchor end eq sub
-- statement:
--   For a source of length n with d deletions, the right boundary anchor is n-d.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L172-L177
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L172-L177

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.matchedAnchor_end_eq_sub (trace : Trace) (n d : ℕ)
    (hsource : trace.source.length = n) (hdel : trace.deletions = d) :
    matchedAnchor trace trace.length = n - d := by sorry
