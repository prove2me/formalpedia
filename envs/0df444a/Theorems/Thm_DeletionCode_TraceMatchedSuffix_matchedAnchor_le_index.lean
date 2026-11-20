-- Prove2me | Theorems.Thm_DeletionCode_TraceMatchedSuffix_matchedAnchor_le_index
-- name    : DeletionCode.TraceMatchedSuffix.matchedAnchor_le_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:34.156514+00:00
-- url     : https://prove2.me/theorems/ebf8bea2-8ab5-4e46-86c7-c332ea555206
-- title:
--   Trace Matched Suffix: matched Anchor le index
-- statement:
--   The Trace Matched Suffix construction uses the matched Anchor le index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L16-L19
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L16-L19

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation

theorem DeletionCode.TraceMatchedSuffix.matchedAnchor_le_index (trace : Trace) (i : ℕ) : trace.matchedAnchor i ≤ i := by sorry
