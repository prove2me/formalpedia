-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_split_column
-- name    : DeletionCode.TraceEditData.split_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:41.266841+00:00
-- url     : https://prove2.me/theorems/cf7c550b-f55c-47bd-8078-18629e0804b3
-- title:
--   Trace Edit Data: split column
-- statement:
--   The selected trace column is recovered from the exact prefix/suffix split.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L201-L208
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L201-L208

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.split_column (trace : Trace) (c : EditColumn trace) :
    trace = trace.take c.val.val ++ column trace c :: trace.drop (c.val.val + 1) := by sorry
