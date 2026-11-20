-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_accuracy_midpoint_exact
-- name    : Aggmetrics.DataStream.accuracy_midpoint_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:04.291418+00:00
-- url     : https://prove2.me/theorems/69d7f527-93d4-4924-8643-ffcba6fb8d75
-- title:
--   Data Stream: accuracy midpoint exact
-- statement:
--   The mid-point rule is exact for the accuracy, which is bilinear in `(R, π)`:
--   `ΔM = π̄ ΔR₁₁ + (1 - π̄) ΔR₀₀ + (R̄₁₁ - R̄₀₀) Δπ`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L237-L242
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L237-L242

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.accuracy_midpoint_exact (R0 S0 π0 R1 S1 π1 : ℝ) :
    accuracy R1 S1 π1 - accuracy R0 S0 π0
      = ((π0 + π1) / 2) * (R1 - R0) + (1 - (π0 + π1) / 2) * (S1 - S0)
        + ((R0 + R1) / 2 - (S0 + S1) / 2) * (π1 - π0) := by sorry
