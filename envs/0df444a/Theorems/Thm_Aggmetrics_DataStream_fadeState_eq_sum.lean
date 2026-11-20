-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fadeState_eq_sum
-- name    : Aggmetrics.DataStream.fadeState_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:59:10.650013+00:00
-- url     : https://prove2.me/theorems/c50ff2d1-431a-44b5-916a-862ad0509c63
-- title:
--   Data Stream: fade State eq sum
-- statement:
--   The fading recurrence computes the weighted sum with the fading weights.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L244-L259
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L244-L259

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fadeState_eq_sum {m : ℕ} (α : ℝ) (y p : ℕ → Fin m → ℝ) (n : ℕ) :
    fadeState α y p n = ∑ k ∈ range n, fadeWeight α n k • outer (y k) (p k) := by sorry
