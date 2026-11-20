-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_tsum_shift
-- name    : Aggmetrics.DataStream.tsum_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:53.256176+00:00
-- url     : https://prove2.me/theorems/73158216-d35e-4bc7-9735-fa13cd689fec
-- title:
--   Data Stream: tsum shift
-- statement:
--   The Data Stream construction uses the tsum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L129-L132
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L129-L132

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.tsum_shift (ρ : ℕ → ℝ) (α : ℝ) :
    ∑' d : ℕ, α ^ (d + 1) * ρ (d + 1) = α * ∑' d : ℕ, α ^ d * ρ (d + 1) := by sorry
