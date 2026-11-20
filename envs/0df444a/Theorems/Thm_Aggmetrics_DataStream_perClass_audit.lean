-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_perClass_audit
-- name    : Aggmetrics.DataStream.perClass_audit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:18:01.463187+00:00
-- url     : https://prove2.me/theorems/358b0960-6c25-4950-8fec-164bf5a4d883
-- title:
--   Data Stream: per Class audit
-- statement:
--   **Audit property.** `exclude` and `nan` never report a number for an unsupported class.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L308-L311
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L308-L311

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.perClass_audit {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m)
    (hj : u j = false) :
    perClass "exclude" u v j = none ∧ perClass "nan" u v j = none := by sorry
