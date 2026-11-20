-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_source_split
-- name    : DeletionCode.TraceEditData.source_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:37.747418+00:00
-- url     : https://prove2.me/theorems/768856ab-27c6-4d52-93e2-cce490cd5fdb
-- title:
--   Trace Edit Data: source split
-- statement:
--   The Trace Edit Data construction uses the source split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L210-L219
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L210-L219

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.source_split (trace : Trace) (c : EditColumn trace) :
    trace.source = sourcePrefix trace c ++
      Trace.source [column trace c] ++ sourceSuffix trace c := by sorry
