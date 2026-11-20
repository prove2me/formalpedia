-- Prove2me | Theorems.Thm_DeletionCode_TraceMatchedSuffix_matchedCount_le_length
-- name    : DeletionCode.TraceMatchedSuffix.matchedCount_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:14.008519+00:00
-- url     : https://prove2.me/theorems/3cacbf37-91bc-484e-9d03-dd9c11638684
-- title:
--   Trace Matched Suffix: matched Count le length
-- statement:
--   The Trace Matched Suffix construction uses the matched Count le length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L12-L14
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L12-L14

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation

theorem DeletionCode.TraceMatchedSuffix.matchedCount_le_length (trace : Trace) : trace.matchedCount ≤ trace.length := by sorry
