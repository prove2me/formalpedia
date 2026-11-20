-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fadeWeight_nonneg
-- name    : Aggmetrics.DataStream.fadeWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:36.084696+00:00
-- url     : https://prove2.me/theorems/a90bf9a7-2a5e-4cfd-be83-2196b5abd398
-- title:
--   Data Stream: fade Weight nonneg
-- statement:
--   The Data Stream construction uses the fade Weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L227-L228
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L227-L228

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fadeWeight_nonneg {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n k : ℕ) : 0 ≤ fadeWeight α n k := by sorry
