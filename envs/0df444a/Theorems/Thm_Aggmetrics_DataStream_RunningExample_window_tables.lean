-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_RunningExample_window_tables
-- name    : Aggmetrics.DataStream.RunningExample.window_tables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:00:27.180572+00:00
-- url     : https://prove2.me/theorems/1fd18ba8-1943-4556-8b56-6c9a238526ce
-- title:
--   Running Example: window tables
-- statement:
--   The per-class tables of the window state at `t = 8`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean#L56-L64
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean#L56-L64

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamExample
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream Aggmetrics.DataStream.RunningExample

theorem Aggmetrics.DataStream.RunningExample.window_tables :
    classTable (winState 4 y p 8) 0 = !![1 / 4, 0; 0, 3 / 4] ∧
    classTable (winState 4 y p 8) 1 = !![1 / 2, 1 / 4; 0, 1 / 4] ∧
    classTable (winState 4 y p 8) 2 = !![0, 0; 1 / 4, 3 / 4] := by sorry
