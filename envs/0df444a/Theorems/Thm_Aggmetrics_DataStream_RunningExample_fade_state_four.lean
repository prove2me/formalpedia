-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_RunningExample_fade_state_four
-- name    : Aggmetrics.DataStream.RunningExample.fade_state_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:03:20.668824+00:00
-- url     : https://prove2.me/theorems/3a91a8e1-32f7-4adb-b68c-9aba6ed743f4
-- title:
--   Running Example: fade state four
-- statement:
--   Exponential fading with `α = 1/2`: the state after the first four instances.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean#L37-L41
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean#L37-L41

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamExample
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream Aggmetrics.DataStream.RunningExample

theorem Aggmetrics.DataStream.RunningExample.fade_state_four :
    fadeState (1 / 2) y p 4 = !![1 / 16, 1 / 4, 0; 0, 1 / 8, 0; 0, 0, 1 / 2] := by sorry
