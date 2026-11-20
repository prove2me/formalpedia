-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_variance_scaling_limit
-- name    : Aggmetrics.DataStream.variance_scaling_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:56:06.276169+00:00
-- url     : https://prove2.me/theorems/a714ce13-e6f3-4533-80b7-af3640318f17
-- title:
--   Data Stream: variance scaling limit
-- statement:
--   Proposition, variance half of "Asymptotic Expectation and Variance Scaling":
--   treating the per-instance variance `v = [V_inst]_{jk}` as a fixed nonnegative real constant under
--   a stationary `P_0` (the paper's own reduction), and the geometric unrolling `Var(C_α(t)) =
--   (1-α)^2 ∑_{k<t} α^{2k} v` of the fading recurrence as given, the `t → ∞` limit is exactly
--   `(1-α)/(1+α) * v`. Note: the paper's further step `≈ v / (2 n_eff)` with `n_eff = 1/(1-α)` is
--   only an *approximation* valid as `α → 1` (it is not an exact identity for general `α`), so it is
--   deliberately left out of this exact-limit statement.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L155-L183
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L155-L183

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.variance_scaling_limit (α v : ℝ) (hα1 : 0 < α) (hα2 : α < 1) :
    Filter.Tendsto (fun t : ℕ => (1 - α) ^ 2 * (∑ k ∈ Finset.range t, α ^ (2 * k)) * v)
      Filter.atTop (nhds ((1 - α) / (1 + α) * v)) := by sorry
