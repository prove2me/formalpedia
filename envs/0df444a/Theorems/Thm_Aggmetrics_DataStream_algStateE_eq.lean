-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_algStateE_eq
-- name    : Aggmetrics.DataStream.algStateE_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:15.311247+00:00
-- url     : https://prove2.me/theorems/ccc0f7b0-9e8d-4e23-8e13-25e085845b13
-- title:
--   Data Stream: alg State E eq
-- statement:
--   The state with eviction is the unified state minus the discarded corrections.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L266-L272
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L266-L272

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.algStateE_eq {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (n : ℕ) :
    algStateE α ε y yt p aud arr n
      = (∑ k ∈ range n, fadeWeight α n k • outer (zvec y yt aud arr n k) (p k))
        - lostState α ε y yt p aud arr n := by sorry
