-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_undefined_window_fading_lower
-- name    : Aggmetrics.DataStream.undefined_window_fading_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:37.24318+00:00
-- url     : https://prove2.me/theorems/32249d3f-abb0-469f-a0b3-49a4c6531c03
-- title:
--   Data Stream: undefined window fading lower
-- statement:
--   Lower bound: if `α^k ≤ ε`, then `k` silent steps leave a class with mass at most `ε`, so the
--   class is unsupported with probability at least `(1 - p)^k`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L118-L147
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L118-L147

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.undefined_window_fading_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (p : ℝ) (hp : ∀ i, (μ (A i)).toReal = p)
    {α ε : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t k : ℕ) (hk : α ^ k ≤ ε) :
    (1 - p) ^ k ≤ (μ {ω | ∑ s ∈ range t,
        (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε}).toReal := by sorry
