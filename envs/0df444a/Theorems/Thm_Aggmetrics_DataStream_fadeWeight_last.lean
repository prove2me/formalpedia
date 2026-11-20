-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fadeWeight_last
-- name    : Aggmetrics.DataStream.fadeWeight_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:38.52718+00:00
-- url     : https://prove2.me/theorems/3725d1ee-0cf9-4164-80e8-c7f64abd1774
-- title:
--   Data Stream: fade Weight last
-- statement:
--   The Data Stream construction uses the fade Weight last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L147-L148
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L147-L148

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fadeWeight_last (α : ℝ) (n : ℕ) : fadeWeight α (n + 1) n = 1 - α := by sorry
