-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_hasDerivAt_ratio_lin
-- name    : Aggmetrics.DataStream.hasDerivAt_ratio_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:52.088183+00:00
-- url     : https://prove2.me/theorems/07d3b84a-983f-42b0-9f35-3192410c62be
-- title:
--   Data Stream: has Deriv At ratio lin
-- statement:
--   The Data Stream construction uses the has Deriv At ratio lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L127-L132
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L127-L132

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.hasDerivAt_ratio_lin (a b c d x D : ℝ) (hD : c * x + d = D) (hD0 : D ≠ 0) :
    HasDerivAt (fun y => (a * y + b) / (c * y + d)) ((a * D - (a * x + b) * c) / D ^ 2) x := by sorry
