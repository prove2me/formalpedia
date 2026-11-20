-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_target_split_of_deletion
-- name    : DeletionCode.TraceEditData.target_split_of_deletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:47:27.040196+00:00
-- url     : https://prove2.me/theorems/11b40831-78da-40d3-84fa-689d2a0956fa
-- title:
--   Trace Edit Data: target split of deletion
-- statement:
--   The Trace Edit Data construction uses the target split of deletion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L242-L245
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L242-L245

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.target_split_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) :
    trace.target = targetPrefix trace c ++ targetSuffix trace c := by sorry
