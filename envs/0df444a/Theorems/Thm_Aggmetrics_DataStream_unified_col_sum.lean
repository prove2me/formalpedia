-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_unified_col_sum
-- name    : Aggmetrics.DataStream.unified_col_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:41.720692+00:00
-- url     : https://prove2.me/theorems/532ae2cc-e6df-4e27-b175-666722348546
-- title:
--   Data Stream: unified col sum
-- statement:
--   The column sums of the unified state are those of the oracle state: the stand-in changes the
--   label side (rows) of the state and not the prediction side (columns).
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L120-L136
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L120-L136

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.unified_col_sum {m n : ℕ} (w O : Fin n → ℝ) (y yt p : Fin n → Fin m → ℝ)
    (hy : ∀ k, ∑ a, y k a = 1) (hyt : ∀ k, ∑ a, yt k a = 1) (b : Fin m) :
    ∑ a, unified w O y yt p a b = ∑ k, w k * p k b := by sorry
