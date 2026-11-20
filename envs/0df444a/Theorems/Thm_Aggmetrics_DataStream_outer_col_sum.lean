-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_outer_col_sum
-- name    : Aggmetrics.DataStream.outer_col_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:47.764667+00:00
-- url     : https://prove2.me/theorems/e60bbc09-5e17-4b31-97a6-ed50691acbb6
-- title:
--   Data Stream: outer col sum
-- statement:
--   The Data Stream construction uses the outer col sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L40-L42
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L40-L42

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.outer_col_sum {m : ℕ} (yt p : Fin m → ℝ) (hy : ∑ a, yt a = 1) (b : Fin m) :
    ∑ a, outer yt p a b = p b := by sorry
