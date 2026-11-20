-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_evicted_change_bound
-- name    : Aggmetrics.DataStream.evicted_change_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:50.917858+00:00
-- url     : https://prove2.me/theorems/0bf8c33d-0622-41e8-84f5-9c9b0ebe1a35
-- title:
--   Data Stream: evicted change bound
-- statement:
--   Late corrections that are evicted change the state by at most the tail mass `α^s` per entry,
--   if each correction has entries bounded by one (as `y pᵀ - ỹ pᵀ` has for probability vectors).
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L263-L282
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L263-L282

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.evicted_change_bound {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (s : ℕ) (S : Finset ℕ)
    (hS : ∀ j ∈ S, s ≤ j) (d : ℕ → ℝ) (hd : ∀ j, |d j| ≤ 1) :
    |∑ j ∈ S, (1 - α) * α ^ j * d j| ≤ α ^ s := by sorry
