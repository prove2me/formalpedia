-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_winWeight_sum
-- name    : Aggmetrics.DataStream.winWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:03:06.840146+00:00
-- url     : https://prove2.me/theorems/14ea2435-d54e-4261-ab11-260d25871ca0
-- title:
--   Data Stream: win Weight sum
-- statement:
--   Once the window has filled, its weights sum to one.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L277-L289
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L277-L289

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.winWeight_sum {W n : ℕ} (hW : 0 < W) (hWn : W ≤ n) :
    ∑ k ∈ range n, winWeight W n k = 1 := by sorry
