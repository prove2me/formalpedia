-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_algState_sub_algStateE
-- name    : Aggmetrics.DataStream.algState_sub_algStateE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:05.345861+00:00
-- url     : https://prove2.me/theorems/eb50e1a1-265e-47a8-9a70-ab90c5693bbd
-- title:
--   Data Stream: alg State sub alg State E
-- statement:
--   **Exact effect of eviction.** The state of the algorithm without eviction exceeds the state
--   with eviction by the sum of the discarded corrections.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L141-L263
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L141-L263

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.algState_sub_algStateE {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (n : ℕ) :
    algState α y yt p aud arr n - algStateE α ε y yt p aud arr n
      = lostState α ε y yt p aud arr n := by sorry
