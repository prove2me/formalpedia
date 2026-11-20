-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_kappa_iid
-- name    : Aggmetrics.DataStream.kappa_iid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:45.41592+00:00
-- url     : https://prove2.me/theorems/c8c435fd-21a5-4650-b6b0-8c0343b2cc2c
-- title:
--   Data Stream: kappa iid
-- statement:
--   Independent entries: `κ = 1`, and the limit is the `(1-α)/(1+α) v` of the paper.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L250-L253
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L250-L253

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.kappa_iid (α : ℝ) :
    kappaVar (fun d => if d = 0 then 1 else 0) α = (1 - α) / (1 + α) := by sorry
