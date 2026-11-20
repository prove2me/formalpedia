-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_oneEditTarget_of_insertion
-- name    : DeletionCode.TraceEditData.oneEditTarget_of_insertion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:41.92503+00:00
-- url     : https://prove2.me/theorems/651c8c54-a724-4b03-886b-468107c45116
-- title:
--   Trace Edit Data: one Edit Target of insertion
-- statement:
--   The Trace Edit Data construction uses the one Edit Target of insertion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L78-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L78-L82

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.oneEditTarget_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) :
    oneEditTarget trace c = trace.source.take (position trace c) ++
      b :: trace.source.drop (position trace c) := by sorry
