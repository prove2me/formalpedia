-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_sel_zero
-- name    : Aggmetrics.DataStream.sel_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:57:40.585921+00:00
-- url     : https://prove2.me/theorems/542407e3-f28a-4c86-aeb2-ecac2fe0e42c
-- title:
--   Data Stream: sel zero
-- statement:
--   The Data Stream construction uses the sel zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L113-L113
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L113-L113

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.sel_zero {m : ℕ} (j l : Fin m) : sel j 0 l = if l = j then 1 else 0 := by sorry
