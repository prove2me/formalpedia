-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_target_split
-- name    : DeletionCode.TraceEditData.target_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:57.683919+00:00
-- url     : https://prove2.me/theorems/d4040296-074e-4201-aadb-0ba6e0e3849c
-- title:
--   Trace Edit Data: target split
-- statement:
--   The Trace Edit Data construction uses the target split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L221-L230
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L221-L230

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.target_split (trace : Trace) (c : EditColumn trace) :
    trace.target = targetPrefix trace c ++
      Trace.target [column trace c] ++ targetSuffix trace c := by sorry
