-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_classTable_TP
-- name    : Aggmetrics.DataStream.classTable_TP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:01:34.949875+00:00
-- url     : https://prove2.me/theorems/8bff89bb-fc05-4293-8dd1-9c953d1f2f32
-- title:
--   Data Stream: class Table TP
-- statement:
--   The Data Stream construction uses the class Table TP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L105-L107
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L105-L107

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.classTable_TP {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 0 0 = C j j := by sorry
