-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_sum_ne_mul
-- name    : Aggmetrics.DataStream.sum_ne_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:57:45.192707+00:00
-- url     : https://prove2.me/theorems/6cbf72b2-f2c0-4f0f-bb40-8d3fdb6b1efe
-- title:
--   Data Stream: sum ne mul
-- statement:
--   The Data Stream construction uses the sum ne mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L117-L125
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L117-L125

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.sum_ne_mul {m : ℕ} (f : Fin m → ℝ) (j : Fin m) :
    ∑ x, (if x = j then (0 : ℝ) else 1) * f x = ∑ x ∈ univ.erase j, f x := by sorry
