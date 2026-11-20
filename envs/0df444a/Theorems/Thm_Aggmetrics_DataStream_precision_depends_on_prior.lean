-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_precision_depends_on_prior
-- name    : Aggmetrics.DataStream.precision_depends_on_prior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:43.74898+00:00
-- url     : https://prove2.me/theorems/1b735e56-22c3-4ce5-907e-5d83485ec0c4
-- title:
--   Data Stream: precision depends on prior
-- statement:
--   Unlike the canonical coordinates, the precision depends on the prior: with
--   `R₁₁ = R₀₀ = 0.85`, it is `0.85` at `π = 1/2` and `17/74` at `π = 1/20`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L61-L66
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L61-L66

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.precision_depends_on_prior :
    precision (17 / 20) (17 / 20) (1 / 2) = 17 / 20 ∧
    precision (17 / 20) (17 / 20) (1 / 20) = 17 / 74 ∧
    precision (17 / 20) (17 / 20) (1 / 2) ≠ precision (17 / 20) (17 / 20) (1 / 20) := by sorry
