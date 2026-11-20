-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fading_variance_autocorr
-- name    : Aggmetrics.DataStream.fading_variance_autocorr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:30.207603+00:00
-- url     : https://prove2.me/theorems/fceb988d-ce7a-4813-a185-1885bac28937
-- title:
--   Data Stream: fading variance autocorr
-- statement:
--   **Variance of the fading estimator with dependent entries**, exact for every `t`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L47-L58
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L47-L58

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fading_variance_autocorr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (ρ : ℕ → ℝ)
    (hcov : ∀ i j, cov[X i, X j; μ] = v * ρ (Int.natAbs ((i : ℤ) - j))) (α : ℝ) (t : ℕ) :
    Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ] = v * covSum ρ α t := by sorry
