-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_outer_row_sum
-- name    : Aggmetrics.DataStream.outer_row_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:37.794363+00:00
-- url     : https://prove2.me/theorems/75e84d6f-86fe-456e-a5dd-51107e490845
-- title:
--   Data Stream: outer row sum
-- statement:
--   The Data Stream construction uses the outer row sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L36-L38
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L36-L38

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.outer_row_sum {m : ℕ} (yt p : Fin m → ℝ) (hp : ∑ b, p b = 1) (a : Fin m) :
    ∑ b, outer yt p a b = yt a := by sorry
