-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_eviction_entry_bound
-- name    : Aggmetrics.DataStream.eviction_entry_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:11.243652+00:00
-- url     : https://prove2.me/theorems/be07dd2c-8367-4ea1-bc29-c328d06416d3
-- title:
--   Data Stream: eviction entry bound
-- statement:
--   **Eviction changes each entry of the state by at most the tail mass `α^s`**, where `s` is the
--   first age whose weight is below `ε`, if the label and prediction vectors have entries in `[0,1]`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L333-L352
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L333-L352

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.eviction_entry_bound {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (h0 : 0 ≤ α) (h1 : α < 1)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1)
    {s : ℕ} (hs : ∀ j, (1 - α) * α ^ j < ε → s ≤ j) (n : ℕ) (a b : Fin m) :
    |(algState α y yt p aud arr n - algStateE α ε y yt p aud arr n) a b| ≤ α ^ s := by sorry
