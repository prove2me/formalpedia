-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_defect_min_example
-- name    : Aggmetrics.DataStream.defect_min_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:45.445821+00:00
-- url     : https://prove2.me/theorems/f376c1e9-fdc5-4eb1-bab2-e842aaa780c1
-- title:
--   Data Stream: defect min example
-- statement:
--   The minimum `t`-norm has marginal defect `3/2` on the running example.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L61-L62
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L61-L62

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.defect_min_example : defect (fun x y => min x y) softEx softEx = 3 / 2 := by sorry
