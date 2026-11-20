-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fadeState_eq_state
-- name    : Aggmetrics.DataStream.fadeState_eq_state
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:44.750784+00:00
-- url     : https://prove2.me/theorems/47651891-c2e6-4c43-aced-2b672bc46086
-- title:
--   Data Stream: fade State eq state
-- statement:
--   The fading recurrence is the temporal state `Yᵀ W P` with the fading weights.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L262-L267
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L262-L267

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fadeState_eq_state {m : ℕ} (α : ℝ) (y p : ℕ → Fin m → ℝ) (n : ℕ) :
    fadeState α y p n
      = state (fun k : Fin n => fadeWeight α n k) (fun k => y k) (fun k => p k) := by sorry
