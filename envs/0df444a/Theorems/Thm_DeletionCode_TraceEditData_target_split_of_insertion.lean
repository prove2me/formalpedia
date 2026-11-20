-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_target_split_of_insertion
-- name    : DeletionCode.TraceEditData.target_split_of_insertion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:47:27.664584+00:00
-- url     : https://prove2.me/theorems/99ed6223-f968-4629-ad61-218920543f62
-- title:
--   Trace Edit Data: target split of insertion
-- statement:
--   The Trace Edit Data construction uses the target split of insertion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L247-L250
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L247-L250

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.target_split_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) :
    trace.target = targetPrefix trace c ++ b :: targetSuffix trace c := by sorry
