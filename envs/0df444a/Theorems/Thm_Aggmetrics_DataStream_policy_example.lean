-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_policy_example
-- name    : Aggmetrics.DataStream.policy_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:18:13.682961+00:00
-- url     : https://prove2.me/theorems/7b253904-2071-4dd5-bb64-1127ad7e6605
-- title:
--   Data Stream: policy example
-- statement:
--   Running example: the recalls `(1, 2/3, undefined)` with support `(1, 1, 0)` give `5/6` under
--   `exclude`, `5/9` under `zero` and no value under `nan`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L351-L361
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L351-L361

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.policy_example :
    macroExclude ![true, true, false] ![1, 2 / 3, 0] = some (5 / 6) ∧
    macroZero ![true, true, false] ![1, 2 / 3, 0] = some (5 / 9) ∧
    macroNan ![true, true, false] ![1, 2 / 3, 0] = none := by sorry
