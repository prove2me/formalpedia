-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_classTable_sum
-- name    : Aggmetrics.DataStream.classTable_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:58:44.062408+00:00
-- url     : https://prove2.me/theorems/77d95488-a661-4d31-a958-ccc0b661bdd9
-- title:
--   Data Stream: class Table sum
-- statement:
--   Commutation: the congruence `S_j · S_jᵀ` is linear in the state.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L82-L84
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L82-L84

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.classTable_sum {m n : ℕ} (c : Fin n → ℝ) (C : Fin n → Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable (∑ k, c k • C k) j = ∑ k, c k • classTable (C k) j := by sorry
