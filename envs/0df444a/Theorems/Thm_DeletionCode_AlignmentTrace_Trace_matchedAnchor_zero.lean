-- Prove2me | Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
-- name    : DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:42.56399+00:00
-- url     : https://prove2.me/theorems/4a488345-2813-4602-9670-a25577701986
-- title:
--   Trace: matched Anchor zero
-- statement:
--   The Trace construction uses the matched Anchor zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L148-L148
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean#L148-L148

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace

theorem DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero (trace : Trace) : matchedAnchor trace 0 = 0 := by sorry

attribute [defeq] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
