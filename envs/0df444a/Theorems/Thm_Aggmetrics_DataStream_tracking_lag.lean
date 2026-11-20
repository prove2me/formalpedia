-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_tracking_lag
-- name    : Aggmetrics.DataStream.tracking_lag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:30:03.55197+00:00
-- url     : https://prove2.me/theorems/d784ee05-112a-4917-8180-7dfd01f45e08
-- title:
--   Data Stream: tracking lag
-- statement:
--   **Tracking lag.** For a population that drifts at a steady velocity `d`,
--   `pop n = a + n d`, and the fading recurrence `c (n+1) = α c n + (1-α) pop (n+1)`, the error is
--   `c n - pop n = L + α^n (c 0 - pop 0 - L)` with `L = -α d/(1-α)`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L270-L285
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L270-L285

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.tracking_lag (α a d : ℝ) (h1 : α < 1) (c : ℕ → ℝ)
    (hc : ∀ n, c (n + 1) = α * c n + (1 - α) * (a + (n + 1 : ℕ) * d)) (n : ℕ) :
    c n - (a + n * d) = -(α * d) / (1 - α) + α ^ n * (c 0 - a + α * d / (1 - α)) := by sorry
