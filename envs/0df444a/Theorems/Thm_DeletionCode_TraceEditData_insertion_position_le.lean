-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_insertion_position_le
-- name    : DeletionCode.TraceEditData.insertion_position_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:47:32.363223+00:00
-- url     : https://prove2.me/theorems/ba3b9142-baa8-4fb9-a21b-d68637f0f1fd
-- title:
--   Trace Edit Data: insertion position le
-- statement:
--   The Trace Edit Data construction uses the insertion position le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L274-L279
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L274-L279

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.insertion_position_le (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) : position trace c ≤ trace.source.length := by sorry
