-- Prove2me | Theorems.Thm_DeletionCode_TraceMatchedSuffix_matched_projections
-- name    : DeletionCode.TraceMatchedSuffix.matched_projections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:38.689434+00:00
-- url     : https://prove2.me/theorems/63170943-77f7-4779-b13a-e22f15edf384
-- title:
--   Trace Matched Suffix: matched projections
-- statement:
--   A trace made entirely of matched columns has identical projections,
--   and each column contributes one letter to that word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L34-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L34-L50

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation

theorem DeletionCode.TraceMatchedSuffix.matched_projections (trace : Trace)
    (hmatched : ∀ col ∈ trace, col.isEdit = false) :
    trace.source = trace.target ∧ trace.source.length = trace.length := by sorry
