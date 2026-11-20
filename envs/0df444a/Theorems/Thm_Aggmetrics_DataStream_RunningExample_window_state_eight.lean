-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_RunningExample_window_state_eight
-- name    : Aggmetrics.DataStream.RunningExample.window_state_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:59:57.323231+00:00
-- url     : https://prove2.me/theorems/55962b06-4c99-4e92-8415-21b04c9ac956
-- title:
--   Running Example: window state eight
-- statement:
--   Sliding window `W = 4`: the state at `t = 8` covers instances `5` to `8`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean#L44-L48
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean#L44-L48

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamExample
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream Aggmetrics.DataStream.RunningExample

theorem Aggmetrics.DataStream.RunningExample.window_state_eight :
    winState 4 y p 8 = !![1 / 4, 0, 0; 0, 1 / 2, 1 / 4; 0, 0, 0] := by sorry
