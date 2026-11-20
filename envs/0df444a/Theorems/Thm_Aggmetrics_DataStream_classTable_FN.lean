-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_classTable_FN
-- name    : Aggmetrics.DataStream.classTable_FN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:01:31.547651+00:00
-- url     : https://prove2.me/theorems/85afdcff-59a8-488a-9a60-7ec32fd1ca45
-- title:
--   Data Stream: class Table FN
-- statement:
--   The Data Stream construction uses the class Table FN property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L127-L133
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L127-L133

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.classTable_FN {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 0 1 = ∑ b ∈ univ.erase j, C j b := by sorry
