-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fadeWeight_succ
-- name    : Aggmetrics.DataStream.fadeWeight_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:33.591352+00:00
-- url     : https://prove2.me/theorems/e4036ab5-ddea-4d14-8a62-7427a21d9796
-- title:
--   Data Stream: fade Weight succ
-- statement:
--   The Data Stream construction uses the fade Weight succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L140-L145
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L140-L145

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fadeWeight_succ {α : ℝ} {n k : ℕ} (hk : k < n) :
    fadeWeight α (n + 1) k = α * fadeWeight α n k := by sorry
