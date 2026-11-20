-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_perClass_default
-- name    : Aggmetrics.DataStream.perClass_default
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:51.466875+00:00
-- url     : https://prove2.me/theorems/cbb7d703-c51d-4e0d-9483-6e47aa222768
-- title:
--   Data Stream: per Class default
-- statement:
--   `zero` and `one` always report a number, supported or not.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L314-L317
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L314-L317

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.perClass_default {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m) :
    (perClass "zero" u v j).isSome ∧ (perClass "one" u v j).isSome := by sorry
