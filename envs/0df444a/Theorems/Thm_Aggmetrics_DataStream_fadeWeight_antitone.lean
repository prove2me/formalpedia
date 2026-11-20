-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fadeWeight_antitone
-- name    : Aggmetrics.DataStream.fadeWeight_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:13.760526+00:00
-- url     : https://prove2.me/theorems/ce96500f-38b8-49c0-bbd3-f4dec5dc3f2c
-- title:
--   Data Stream: fade Weight antitone
-- statement:
--   The Data Stream construction uses the fade Weight antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L32-L36
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L32-L36

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fadeWeight_antitone {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {n n' k : ℕ} (hnn : n ≤ n') :
    fadeWeight α n' k ≤ fadeWeight α n k := by sorry
