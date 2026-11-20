-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_classTable_nonneg
-- name    : Aggmetrics.DataStream.classTable_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:58:52.419191+00:00
-- url     : https://prove2.me/theorems/be27a9bf-f856-47cd-914c-8faa813cadbd
-- title:
--   Data Stream: class Table nonneg
-- statement:
--   The Data Stream construction uses the class Table nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L92-L96
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L92-L96

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.classTable_nonneg {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} (hC : ∀ a b, 0 ≤ C a b)
    (j : Fin m) (r s : Fin 2) : 0 ≤ classTable C j r s := by sorry
