-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_accuracy_partials
-- name    : Aggmetrics.DataStream.accuracy_partials
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:23.832211+00:00
-- url     : https://prove2.me/theorems/5449a78f-af4f-4edf-8e92-c6be04caf4a9
-- title:
--   Data Stream: accuracy partials
-- statement:
--   The partials of the accuracy: `π`, `1 - π` and `R₁₁ - R₀₀`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L213-L224
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L213-L224

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.accuracy_partials (R S π : ℝ) :
    HasDerivAt (fun y => accuracy y S π) π R ∧ HasDerivAt (fun y => accuracy R y π) (1 - π) S ∧
      HasDerivAt (fun y => accuracy R S y) (R - S) π := by sorry
