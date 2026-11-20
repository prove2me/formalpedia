-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_iIndepSet_compl_meas_biInter
-- name    : Aggmetrics.DataStream.iIndepSet_compl_meas_biInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:35.981734+00:00
-- url     : https://prove2.me/theorems/2cbb8341-3672-4e91-814e-e5cb4abc4ee9
-- title:
--   Data Stream: i Indep Set compl meas bi Inter
-- statement:
--   The complements of independent events are independent: the probability of the intersection
--   of the complements over a finite set is the product of the probabilities of the complements.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L37-L44
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L37-L44

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.iIndepSet_compl_meas_biInter {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ι → Set Ω) (hA : iIndepSet A μ) (S : Finset ι) :
    μ (⋂ i ∈ S, (A i)ᶜ) = ∏ i ∈ S, μ (A i)ᶜ := by sorry
