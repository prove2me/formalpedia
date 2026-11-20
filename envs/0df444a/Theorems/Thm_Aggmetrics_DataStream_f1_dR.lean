-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_f1_dR
-- name    : Aggmetrics.DataStream.f1_dR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:40.751175+00:00
-- url     : https://prove2.me/theorems/aed54b7c-a83f-430f-a88c-052fd2080193
-- title:
--   Data Stream: f1 d R
-- statement:
--   `∂ F₁ / ∂R₁₁ = 2π[π + (1-π)(1-R₀₀)] / D²`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L174-L184
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L174-L184

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.f1_dR (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 y S π)
      (2 * π * (π + (1 - π) * (1 - S)) / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) R := by sorry
