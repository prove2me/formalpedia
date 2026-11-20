-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fade_tail_sum
-- name    : Aggmetrics.DataStream.fade_tail_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:43.903334+00:00
-- url     : https://prove2.me/theorems/0c1735d5-f500-4427-807e-27e2e86dafc9
-- title:
--   Data Stream: fade tail sum
-- statement:
--   The tail of the fading weights from age `s` on carries mass exactly `α^s`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L235-L243
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L235-L243

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fade_tail_sum {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (s : ℕ) :
    HasSum (fun j : ℕ => (1 - α) * α ^ (s + j)) (α ^ s) := by sorry
