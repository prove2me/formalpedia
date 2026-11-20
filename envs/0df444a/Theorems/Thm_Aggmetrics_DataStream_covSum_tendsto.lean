-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_covSum_tendsto
-- name    : Aggmetrics.DataStream.covSum_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:22.526187+00:00
-- url     : https://prove2.me/theorems/c6237827-f6e1-4522-bf58-30e45e49010f
-- title:
--   Data Stream: cov Sum tendsto
-- statement:
--   **The double sum converges to `V = (1-α)/(1+α) κ(α)`.**
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L224-L233
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L224-L233

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.covSum_tendsto {ρ : ℕ → ℝ} (hρ0 : ρ 0 = 1) (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α < 1) :
    Tendsto (fun t => covSum ρ α t) atTop (𝓝 (kappaVar ρ α)) := by sorry
