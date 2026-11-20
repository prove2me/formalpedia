-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_latency_const_delay
-- name    : Aggmetrics.DataStream.latency_const_delay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:29.447809+00:00
-- url     : https://prove2.me/theorems/db0c338e-e7b3-41dd-98a4-550dea2bc143
-- title:
--   Data Stream: latency const delay
-- statement:
--   A constant delay `Δ ≤ W`: the factors of the first `Δ` ages are `1` and the others `1 - pb`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L80-L94
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L80-L94

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.latency_const_delay (pb : ℝ) (Δ W : ℕ) (hΔ : Δ ≤ W) :
    ∏ s ∈ range W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = (1 - pb) ^ (W - Δ) := by sorry
