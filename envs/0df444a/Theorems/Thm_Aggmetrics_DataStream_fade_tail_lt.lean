-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fade_tail_lt
-- name    : Aggmetrics.DataStream.fade_tail_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:45.413885+00:00
-- url     : https://prove2.me/theorems/39145ac2-a4ff-4346-b4c0-e4e2b1beefc0
-- title:
--   Data Stream: fade tail lt
-- statement:
--   If the weight of an entry of age `s` is below `ε`, the tail from `s` on carries less than
--   `ε n_eff`, with `n_eff = 1/(1-α)`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L247-L251
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L247-L251

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fade_tail_lt {α ε : ℝ} (h1 : α < 1) (s : ℕ) (hs : (1 - α) * α ^ s < ε) :
    α ^ s < ε * (1 / (1 - α)) := by sorry
