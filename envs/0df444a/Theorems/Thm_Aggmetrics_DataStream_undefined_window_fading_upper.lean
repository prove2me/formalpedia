-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_undefined_window_fading_upper
-- name    : Aggmetrics.DataStream.undefined_window_fading_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:46.753176+00:00
-- url     : https://prove2.me/theorems/289e640f-1043-4ad5-9d8d-62e479d347ce
-- title:
--   Data Stream: undefined window fading upper
-- statement:
--   Upper bound: if every age below `k ≤ t` carries a weight above `ε`, an arrival in the last
--   `k` steps keeps the class supported, so it is unsupported with probability at most `(1 - p)^k`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L151-L176
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L151-L176

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.undefined_window_fading_upper {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (p : ℝ) (hp : ∀ i, (μ (A i)).toReal = p)
    {α ε : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t k : ℕ) (hk : ∀ s < k, ε < (1 - α) * α ^ s)
    (hkt : k ≤ t) :
    (μ {ω | ∑ s ∈ range t,
        (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε}).toReal ≤ (1 - p) ^ k := by sorry
