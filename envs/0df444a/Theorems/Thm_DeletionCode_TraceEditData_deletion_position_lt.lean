-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_deletion_position_lt
-- name    : DeletionCode.TraceEditData.deletion_position_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:47:15.454398+00:00
-- url     : https://prove2.me/theorems/3aee50a6-f6aa-478b-9595-2087b980b4f9
-- title:
--   Trace Edit Data: deletion position lt
-- statement:
--   The Trace Edit Data construction uses the deletion position lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L267-L272
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L267-L272

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.deletion_position_lt (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) : position trace c < trace.source.length := by sorry
