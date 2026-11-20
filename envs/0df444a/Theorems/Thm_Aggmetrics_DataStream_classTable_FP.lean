-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_classTable_FP
-- name    : Aggmetrics.DataStream.classTable_FP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:01:31.022004+00:00
-- url     : https://prove2.me/theorems/9727384f-5c7c-4531-8e0c-155455a67942
-- title:
--   Data Stream: class Table FP
-- statement:
--   The Data Stream construction uses the class Table FP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L135-L142
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L135-L142

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.classTable_FP {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 1 0 = ∑ a ∈ univ.erase j, C a j := by sorry
