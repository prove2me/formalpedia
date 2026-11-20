-- Prove2me | Theorems.Thm_DeletionCode_TraceMatchedSuffix_common_suffix_of_matched_range
-- name    : DeletionCode.TraceMatchedSuffix.common_suffix_of_matched_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:16.249219+00:00
-- url     : https://prove2.me/theorems/782930eb-db2e-4fe9-9eab-fa19fcc97683
-- title:
--   Trace Matched Suffix: common suffix of matched range
-- statement:
--   A concrete edit-free interval of columns supplies a common suffix of
--   the source and target prefixes.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L54-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L54-L84

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation

theorem DeletionCode.TraceMatchedSuffix.common_suffix_of_matched_range (trace : Trace) (i m : ℕ)
    (hm : m ≤ i) (hi : i ≤ trace.length)
    (hno : ∀ j : Fin trace.length, i - m ≤ j.val → j.val < i → ¬ EditIndex trace j) :
    ∃ a b common : List Bool,
      Trace.source (trace.take i) = a ++ common ∧
      Trace.target (trace.take i) = b ++ common ∧ common.length = m := by sorry
