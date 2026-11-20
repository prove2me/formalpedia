-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_recall_integral
-- name    : Aggmetrics.DataStream.recall_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:34.612391+00:00
-- url     : https://prove2.me/theorems/3023fa3e-32d5-4ceb-aa31-190c8d406f2d
-- title:
--   Data Stream: recall integral
-- statement:
--   **Recall is free of the prior.** The expected cell masses of the positive class are
--   `π ∫ f dP₁` and `π ∫ (1 - f) dP₁`; their ratio is `∫ f dP₁` for every `π ≠ 0`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L36-L43
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L36-L43

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.recall_integral {X : Type*} [MeasurableSpace X] (P1 : Measure X) [IsProbabilityMeasure P1]
    (f : X → ℝ) (hf : Integrable f P1) (π : ℝ) (hπ : π ≠ 0) :
    (π * ∫ x, f x ∂P1) / (π * ∫ x, f x ∂P1 + π * ∫ x, (1 - f x) ∂P1) = ∫ x, f x ∂P1 := by sorry
