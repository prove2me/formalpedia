-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_state_apply
-- name    : Aggmetrics.DataStream.state_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:57:42.311001+00:00
-- url     : https://prove2.me/theorems/32730fda-8272-406e-bc73-5f8f8be77ace
-- title:
--   Data Stream: state apply
-- statement:
--   The Data Stream construction uses the state apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L58-L60
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L58-L60

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.state_apply {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) (a b : Fin m) :
    state w y p a b = ∑ k, w k * (y k a * p k b) := by sorry
