-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_source_split_of_insertion
-- name    : DeletionCode.TraceEditData.source_split_of_insertion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:23.082567+00:00
-- url     : https://prove2.me/theorems/930a883d-b570-4844-9560-69d13dbe2fcb
-- title:
--   Trace Edit Data: source split of insertion
-- statement:
--   The Trace Edit Data construction uses the source split of insertion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L237-L240
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L237-L240

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.source_split_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) :
    trace.source = sourcePrefix trace c ++ sourceSuffix trace c := by sorry
