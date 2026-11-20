-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_oneEditTarget_deletion_split
-- name    : DeletionCode.TraceEditData.oneEditTarget_deletion_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:50.561993+00:00
-- url     : https://prove2.me/theorems/b26a900c-4638-4ce1-ae03-5dccda50cc4d
-- title:
--   Trace Edit Data: one Edit Target deletion split
-- statement:
--   The Trace Edit Data construction uses the one Edit Target deletion split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L252-L258
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L252-L258

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.oneEditTarget_deletion_split (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) :
    oneEditTarget trace c = sourcePrefix trace c ++ sourceSuffix trace c := by sorry
