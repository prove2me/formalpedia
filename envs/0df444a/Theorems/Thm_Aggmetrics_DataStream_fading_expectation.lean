-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fading_expectation
-- name    : Aggmetrics.DataStream.fading_expectation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:26.825531+00:00
-- url     : https://prove2.me/theorems/f7ae58a6-4b3e-46e8-9a0b-3f8d63b0ba69
-- title:
--   Data Stream: fading expectation
-- statement:
--   **Expectation of the fading estimator**, `E[C_α(t)] = (1 - α^t) C_pop`, for any `t`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L90-L96
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L90-L96

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fading_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hint : ∀ k, Integrable (X k) μ) (c : ℝ)
    (hmean : ∀ k, ∫ ω, X k ω ∂μ = c) (α : ℝ) (t : ℕ) :
    ∫ ω, ∑ k ∈ range t, fadeWeight α t k * X k ω ∂μ = (1 - α ^ t) * c := by sorry
