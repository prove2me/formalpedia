-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fading_variance
-- name    : Aggmetrics.DataStream.fading_variance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:38.746128+00:00
-- url     : https://prove2.me/theorems/48d67f4f-72ea-46f9-8b39-cec6453de6fa
-- title:
--   Data Stream: fading variance
-- statement:
--   **Variance of the fading estimator** for independent entries with variance `v`:
--   `Var(C_α(t)) = (1-α)/(1+α) (1 - α^{2t}) v`, for any `t`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L100-L117
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L100-L117

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fading_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : iIndepFun X μ)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (hvar : ∀ k, Var[X k; μ] = v)
    {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ]
      = (1 - α) / (1 + α) * (1 - α ^ (2 * t)) * v := by sorry
