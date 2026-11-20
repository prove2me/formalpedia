-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_tnorm_hard_min
-- name    : Aggmetrics.DataStream.tnorm_hard_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:49.38911+00:00
-- url     : https://prove2.me/theorems/e8aaed81-c793-4410-85bb-d46e14f01e22
-- title:
--   Data Stream: tnorm hard min
-- statement:
--   On a hard (one-hot) prediction the minimum `t`-norm is the product.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L69-L73
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L69-L73

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.tnorm_hard_min {m : ℕ} (yt : Fin m → ℝ) (hy : ∀ a, 0 ≤ yt a ∧ yt a ≤ 1) (k a b : Fin m) :
    min (yt a) (if b = k then (1 : ℝ) else 0) = yt a * (if b = k then (1 : ℝ) else 0) := by sorry
