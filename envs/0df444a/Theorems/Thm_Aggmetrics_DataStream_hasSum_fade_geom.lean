-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_hasSum_fade_geom
-- name    : Aggmetrics.DataStream.hasSum_fade_geom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:26.078726+00:00
-- url     : https://prove2.me/theorems/43985a4e-8738-4cb8-946c-a889e3e4e75c
-- title:
--   Data Stream: has Sum fade geom
-- statement:
--   The Data Stream construction uses the has Sum fade geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L134-L140
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L134-L140

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.hasSum_fade_geom {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    HasSum (fun i : ℕ => (1 - α) * α ^ (i + t)) (α ^ t) := by sorry
