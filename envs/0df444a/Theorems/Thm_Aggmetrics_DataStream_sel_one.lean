-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_sel_one
-- name    : Aggmetrics.DataStream.sel_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:57:32.010545+00:00
-- url     : https://prove2.me/theorems/aba732bf-935d-4992-8813-64557d8ef5b3
-- title:
--   Data Stream: sel one
-- statement:
--   The Data Stream construction uses the sel one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L115-L115
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L115-L115

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.sel_one {m : ℕ} (j l : Fin m) : sel j 1 l = if l = j then 0 else 1 := by sorry
