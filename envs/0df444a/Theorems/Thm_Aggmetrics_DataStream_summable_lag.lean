-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_summable_lag
-- name    : Aggmetrics.DataStream.summable_lag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:27.699186+00:00
-- url     : https://prove2.me/theorems/da13ccee-5401-467a-a681-16b017fffad3
-- title:
--   Data Stream: summable lag
-- statement:
--   The Data Stream construction uses the summable lag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L142-L152
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L142-L152

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.summable_lag {ρ : ℕ → ℝ} (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    Summable (fun d : ℕ => (1 - α) * α ^ d * ρ (d + 1)) := by sorry
