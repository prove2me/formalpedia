-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_evict_age_exists
-- name    : Aggmetrics.DataStream.evict_age_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:20.87481+00:00
-- url     : https://prove2.me/theorems/d407c4bf-3476-4dbb-8455-afd7f18bf6e4
-- title:
--   Data Stream: evict age exists
-- statement:
--   An age `N` with `(1-α) α^N < ε` exists, and it is at most `n_eff · ln(1/(n_eff ε)) + 2`, with
--   `n_eff = 1/(1-α)`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L73-L113
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L73-L113

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.evict_age_exists {α ε : ℝ} (h0 : 0 < α) (h1 : α < 1) (hε : 0 < ε) :
    ∃ N : ℕ, (1 - α) * α ^ N < ε ∧
      (N : ℝ) ≤ max (Real.log ((1 - α) / ε)) 0 / (1 - α) + 2 := by sorry
