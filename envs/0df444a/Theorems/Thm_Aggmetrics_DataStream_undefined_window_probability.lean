-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_undefined_window_probability
-- name    : Aggmetrics.DataStream.undefined_window_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:55:56.11817+00:00
-- url     : https://prove2.me/theorems/cfa3aa71-b79b-4e6c-be0a-994c3e99b95f
-- title:
--   Data Stream: undefined window probability
-- statement:
--   Proposition (Undefined-Window Probability Under Stationary Arrivals): if the `W`
--   per-position non-arrival events for class `j` are mutually independent (taken directly as the
--   multiplicativity-over-the-full-intersection property that is independence's defining content)
--   and each has the same arrival probability `p`, the probability that class `j` never arrives in
--   the window is exactly `(1-p)^W`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L104-L112
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L104-L112

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.undefined_window_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : ℕ) (A : Fin W → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : μ (⋂ i, (A i)ᶜ) = ∏ i, μ (A i)ᶜ)
    (p : ENNReal) (hp : ∀ i, μ (A i) = p) :
    μ (⋂ i, (A i)ᶜ) = (1 - p) ^ W := by sorry
