-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_lag_tail
-- name    : Aggmetrics.DataStream.lag_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:35.775116+00:00
-- url     : https://prove2.me/theorems/529857ec-9425-42c2-a193-03cc7d006f9b
-- title:
--   Data Stream: lag tail
-- statement:
--   The tail of the lag sum: `|E_t - E_∞| ≤ α^t`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L155-L171
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L155-L171

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.lag_tail {ρ : ℕ → ℝ} (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    |lagSum ρ α t - einf ρ α| ≤ α ^ t := by sorry
