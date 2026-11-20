-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_f1_dS
-- name    : Aggmetrics.DataStream.f1_dS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:58.293279+00:00
-- url     : https://prove2.me/theorems/ad6417f9-0079-4b11-bad4-96e142040927
-- title:
--   Data Stream: f1 d S
-- statement:
--   `∂ F₁ / ∂R₀₀ = 2π(1-π)R₁₁ / D²`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L187-L197
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L187-L197

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.f1_dS (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 R y π)
      (2 * π * (1 - π) * R / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) S := by sorry
