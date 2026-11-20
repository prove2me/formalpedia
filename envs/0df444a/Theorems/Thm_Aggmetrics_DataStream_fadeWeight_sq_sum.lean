-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fadeWeight_sq_sum
-- name    : Aggmetrics.DataStream.fadeWeight_sq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:53.378529+00:00
-- url     : https://prove2.me/theorems/1f490e68-90fa-42e8-a3cf-a043c4317c6b
-- title:
--   Data Stream: fade Weight sq sum
-- statement:
--   The Data Stream construction uses the fade Weight sq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L70-L87
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L70-L87

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fadeWeight_sq_sum {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    ∑ k ∈ range t, (fadeWeight α t k) ^ 2 = (1 - α) / (1 + α) * (1 - α ^ (2 * t)) := by sorry
