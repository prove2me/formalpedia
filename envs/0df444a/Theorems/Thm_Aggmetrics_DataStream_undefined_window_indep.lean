-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_undefined_window_indep
-- name    : Aggmetrics.DataStream.undefined_window_indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:28.10959+00:00
-- url     : https://prove2.me/theorems/b31b8135-d52f-469f-8a59-1588120bcbf2
-- title:
--   Data Stream: undefined window indep
-- statement:
--   Probability that none of the independent events `A i`, `i ∈ S`, occurs.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L47-L54
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L47-L54

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.undefined_window_indep {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ι → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (S : Finset ι) :
    (μ (⋂ i ∈ S, (A i)ᶜ)).toReal = ∏ i ∈ S, (1 - (μ (A i)).toReal) := by sorry
