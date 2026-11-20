-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_latency_delay_ge_window
-- name    : Aggmetrics.DataStream.latency_delay_ge_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:48.648699+00:00
-- url     : https://prove2.me/theorems/930e6b0a-7e66-476b-8e67-9ad9ec8c6243
-- title:
--   Data Stream: latency delay ge window
-- statement:
--   A delay of at least the window: every window is undefined.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L97-L102
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L97-L102

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.latency_delay_ge_window (pb : ℝ) (Δ W : ℕ) (hΔ : W ≤ Δ) :
    ∏ s ∈ range W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = 1 := by sorry
