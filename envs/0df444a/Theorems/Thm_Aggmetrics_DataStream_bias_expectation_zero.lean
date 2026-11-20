-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_bias_expectation_zero
-- name    : Aggmetrics.DataStream.bias_expectation_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:51.528057+00:00
-- url     : https://prove2.me/theorems/fe747e92-281c-4847-bb84-5e56fdf18e34
-- title:
--   Data Stream: bias expectation zero
-- statement:
--   Under calibration (the residual `y - ỹ` has mean zero given the scores and predictions, which
--   are fixed here), the expected bias is zero.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L102-L114
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L102-L114

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.bias_expectation_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n : ℕ}
    (w O : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (y yt : Fin n → Ω → Fin m → ℝ)
    (hint : ∀ k a, Integrable (fun ω => y k ω a - yt k ω a) μ)
    (hcal : ∀ k a, ∫ ω, (y k ω a - yt k ω a) ∂μ = 0) (a b : Fin m) :
    ∫ ω, (∑ k, ((1 - O k) * w k) • outer (fun c => y k ω c - yt k ω c) (p k)) a b ∂μ = 0 := by sorry
