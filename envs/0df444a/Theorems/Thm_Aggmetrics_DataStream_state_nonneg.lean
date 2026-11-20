-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_state_nonneg
-- name    : Aggmetrics.DataStream.state_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:59:05.37746+00:00
-- url     : https://prove2.me/theorems/137ea15e-0629-4956-af6c-dcf3c4e834d3
-- title:
--   Data Stream: state nonneg
-- statement:
--   The Data Stream construction uses the state nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L98-L101
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L98-L101

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.state_nonneg {m n : ℕ} {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) {y p : Fin n → Fin m → ℝ}
    (hy : ∀ k a, 0 ≤ y k a) (hp : ∀ k a, 0 ≤ p k a) (a b : Fin m) : 0 ≤ state w y p a b := by sorry
