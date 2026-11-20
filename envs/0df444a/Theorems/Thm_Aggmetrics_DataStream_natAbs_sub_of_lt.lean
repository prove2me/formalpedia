-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_natAbs_sub_of_lt
-- name    : Aggmetrics.DataStream.natAbs_sub_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:32.531179+00:00
-- url     : https://prove2.me/theorems/6ca013a4-7220-43ac-ac3a-8ae2d5eaacdf
-- title:
--   Data Stream: nat Abs sub of lt
-- statement:
--   The Data Stream construction uses the nat Abs sub of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L62-L65
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L62-L65

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.natAbs_sub_of_lt {i t : ℕ} (h : i < t) : Int.natAbs ((i : ℤ) - (t : ℤ)) = t - i := by sorry
