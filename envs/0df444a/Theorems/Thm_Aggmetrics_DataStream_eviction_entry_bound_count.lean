-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_eviction_entry_bound_count
-- name    : Aggmetrics.DataStream.eviction_entry_bound_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:26.578157+00:00
-- url     : https://prove2.me/theorems/156f554e-ee98-4a00-9c9d-3e8e349298c5
-- title:
--   Data Stream: eviction entry bound count
-- statement:
--   **Eviction changes each entry by less than `ε` per discarded correction.**
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L355-L375
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L355-L375

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.eviction_entry_bound_count {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (h0 : 0 ≤ α) (h1 : α < 1)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1) (n : ℕ) (a b : Fin m) :
    |(algState α y yt p aud arr n - algStateE α ε y yt p aud arr n) a b|
      ≤ ((range n).filter (fun k => discarded α ε aud arr n k)).card * ε := by sorry
