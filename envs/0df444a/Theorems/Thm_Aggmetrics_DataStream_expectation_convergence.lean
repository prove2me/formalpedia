-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_expectation_convergence
-- name    : Aggmetrics.DataStream.expectation_convergence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:56:06.119109+00:00
-- url     : https://prove2.me/theorems/3fd1e6a5-9e0b-44af-8170-8af7ff8b19b7
-- title:
--   Data Stream: expectation convergence
-- statement:
--   Proposition, expectation half of "Asymptotic Expectation and Variance
--   Scaling": unrolling the fading recurrence gives `E[C_α(t)] = (1 - α^t) * C_pop` under a
--   stationary generating distribution (taken here as the starting point, matching the paper's own
--   one-line derivation); this is the `t → ∞` convergence `E[C_α(t)] → C_pop`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L140-L146
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L140-L146

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.expectation_convergence (α c : ℝ) (hα1 : 0 < α) (hα2 : α < 1) :
    Filter.Tendsto (fun t : ℕ => (1 - α ^ t) * c) Filter.atTop (nhds c) := by sorry
