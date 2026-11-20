-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fading_variance_tendsto
-- name    : Aggmetrics.DataStream.fading_variance_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:41.817164+00:00
-- url     : https://prove2.me/theorems/3ed689d0-7d09-426c-9e44-c068b0ade335
-- title:
--   Data Stream: fading variance tendsto
-- statement:
--   **Variance of the fading estimator with dependent entries**: the limit is
--   `v (1-α)/(1+α) κ(α)`, that is, the effective sample size is divided by `κ(α)`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L237-L245
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L237-L245

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fading_variance_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (ρ : ℕ → ℝ)
    (hcov : ∀ i j, cov[X i, X j; μ] = v * ρ (Int.natAbs ((i : ℤ) - j)))
    (hρ0 : ρ 0 = 1) (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    Tendsto (fun t => Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ]) atTop
      (𝓝 (v * kappaVar ρ α)) := by sorry
