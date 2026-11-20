-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_evicted_sum_bound
-- name    : Aggmetrics.DataStream.evicted_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:18.264971+00:00
-- url     : https://prove2.me/theorems/bd861b78-bd1a-4615-9135-08fbb2ea2515
-- title:
--   Data Stream: evicted sum bound
-- statement:
--   The weighted sum of bounded terms over instances of age at least `s` is at most `α^s`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L277-L300
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L277-L300

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.evicted_sum_bound {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (n s : ℕ) (D : Finset ℕ)
    (hD : ∀ k ∈ D, k < n ∧ s ≤ n - 1 - k) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1) :
    |∑ k ∈ D, fadeWeight α n k * d k| ≤ α ^ s := by sorry
