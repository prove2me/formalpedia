-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_recall_prior_invariant
-- name    : Aggmetrics.DataStream.recall_prior_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:55:47.320876+00:00
-- url     : https://prove2.me/theorems/5a2e49e4-8fc9-4af0-9b75-b9eb8e75ba86
-- title:
--   Data Stream: recall prior invariant
-- statement:
--   Proposition (Strict Prior-Invariance of the Canonical Basis), recall coordinate: with
--   `A(t) = π(t) * Recall(t)` and `C(t) = π(t) * (1 - Recall(t))` (law of total probability on the
--   positive class), `A(t) / (A(t) + C(t))` is exactly `Recall(t)`, for every `π(t) ≠ 0`, whatever
--   `f_t` and `P_t(X ∣ Y)` are doing.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L88-L90
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStream.lean#L88-L90

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.recall_prior_invariant (prior r : ℝ) (hprior : prior ≠ 0) :
    (prior * r) / (prior * r + prior * (1 - r)) = r := by sorry
