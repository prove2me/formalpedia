-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fadeWeight_sum
-- name    : Aggmetrics.DataStream.fadeWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:36.543903+00:00
-- url     : https://prove2.me/theorems/84c8a74f-50a6-457d-ade1-fc1fa90aafb7
-- title:
--   Data Stream: fade Weight sum
-- statement:
--   The total mass of the fading weights is `1 - α^n`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L231-L236
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L231-L236

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fadeWeight_sum (α : ℝ) (n : ℕ) : ∑ k ∈ range n, fadeWeight α n k = 1 - α ^ n := by sorry
