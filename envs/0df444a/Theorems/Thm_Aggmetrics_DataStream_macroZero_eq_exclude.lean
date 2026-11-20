-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_macroZero_eq_exclude
-- name    : Aggmetrics.DataStream.macroZero_eq_exclude
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:18:13.836586+00:00
-- url     : https://prove2.me/theorems/2fb8cbd8-878e-4361-b55a-b08c97b38e79
-- title:
--   Data Stream: macro Zero eq exclude
-- statement:
--   `zero` is the `exclude` average shrunk by the share of supported classes.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L337-L347
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L337-L347

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.macroZero_eq_exclude {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (e : ℝ)
    (hne : active u ≠ 0) (hm : (m : ℝ) ≠ 0) (he : macroExclude u v = some e) :
    macroZero u v = some (e * (active u : ℝ) / (m : ℝ)) := by sorry
