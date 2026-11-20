-- Prove2me | Theorems.Thm_DeletionCode_TraceMatchedSuffix_common_suffix_before_edit
-- name    : DeletionCode.TraceMatchedSuffix.common_suffix_before_edit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:39.53202+00:00
-- url     : https://prove2.me/theorems/9df4901c-6c8d-47c1-a7cd-fa46b7ea74a2
-- title:
--   Trace Matched Suffix: common suffix before edit
-- statement:
--   Before any separated edit, at least L-1 consecutive matched columns
--   give an actual common suffix of the two projected prefixes.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L88-L104
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L88-L104

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation

theorem DeletionCode.TraceMatchedSuffix.common_suffix_before_edit {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    ∃ a b common : List Bool,
      Trace.source (trace.take i.val) = a ++ common ∧
      Trace.target (trace.take i.val) = b ++ common ∧ L - 1 ≤ common.length := by sorry
