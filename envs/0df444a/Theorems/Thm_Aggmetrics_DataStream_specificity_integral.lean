-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_specificity_integral
-- name    : Aggmetrics.DataStream.specificity_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:31.916595+00:00
-- url     : https://prove2.me/theorems/47ca6ec6-c1cf-4e6f-963f-8869a823c8d3
-- title:
--   Data Stream: specificity integral
-- statement:
--   **Specificity is free of the prior.**
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L46-L54
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L46-L54

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.specificity_integral {X : Type*} [MeasurableSpace X] (P0 : Measure X)
    [IsProbabilityMeasure P0] (f : X → ℝ) (hf : Integrable f P0) (π : ℝ) (hπ : π ≠ 1) :
    ((1 - π) * ∫ x, (1 - f x) ∂P0)
        / ((1 - π) * ∫ x, (1 - f x) ∂P0 + (1 - π) * ∫ x, f x ∂P0) = ∫ x, (1 - f x) ∂P0 := by sorry
