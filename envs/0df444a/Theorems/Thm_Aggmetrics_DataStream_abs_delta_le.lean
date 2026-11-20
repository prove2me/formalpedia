-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_abs_delta_le
-- name    : Aggmetrics.DataStream.abs_delta_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:04.114172+00:00
-- url     : https://prove2.me/theorems/4a552341-99b4-4fa2-9194-ef64d93a138a
-- title:
--   Data Stream: abs delta le
-- statement:
--   The Data Stream construction uses the abs delta le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L316-L329
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L316-L329

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.abs_delta_le {m : ℕ} (y yt p : ℕ → Fin m → ℝ)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1) (k : ℕ) (a b : Fin m) :
    |(y k a - yt k a) * p k b| ≤ 1 := by sorry
