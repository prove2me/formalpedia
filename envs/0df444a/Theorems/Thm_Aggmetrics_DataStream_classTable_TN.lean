-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_classTable_TN
-- name    : Aggmetrics.DataStream.classTable_TN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:01:36.064502+00:00
-- url     : https://prove2.me/theorems/7da096d0-57e5-4778-9d40-054b33627f63
-- title:
--   Data Stream: class Table TN
-- statement:
--   The Data Stream construction uses the class Table TN property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L144-L156
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L144-L156

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.classTable_TN {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 1 1 = ∑ a ∈ univ.erase j, ∑ b ∈ univ.erase j, C a b := by sorry
