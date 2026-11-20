-- Prove2me | Theorems.Thm_DeletionCode_TraceEditData_oneEditTarget_insertion_split
-- name    : DeletionCode.TraceEditData.oneEditTarget_insertion_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:50.812631+00:00
-- url     : https://prove2.me/theorems/9def3be2-355b-4831-939b-38f4dee29d6c
-- title:
--   Trace Edit Data: one Edit Target insertion split
-- statement:
--   The Trace Edit Data construction uses the one Edit Target insertion split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L260-L265
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean#L260-L265

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DeletionCode_TraceEditData
set_option autoImplicit true
open DeletionCode DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

theorem DeletionCode.TraceEditData.oneEditTarget_insertion_split (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) :
    oneEditTarget trace c = sourcePrefix trace c ++ b :: sourceSuffix trace c := by sorry
