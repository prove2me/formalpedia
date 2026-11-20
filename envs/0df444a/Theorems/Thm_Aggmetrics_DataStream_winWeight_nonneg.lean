-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_winWeight_nonneg
-- name    : Aggmetrics.DataStream.winWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:55.095174+00:00
-- url     : https://prove2.me/theorems/d83700b9-d632-469a-a315-96f7eed12e61
-- title:
--   Data Stream: win Weight nonneg
-- statement:
--   The Data Stream construction uses the win Weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L272-L274
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L272-L274

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.winWeight_nonneg (W n k : ℕ) : 0 ≤ winWeight W n k := by sorry
