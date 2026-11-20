-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_classTable_apply
-- name    : Aggmetrics.DataStream.classTable_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:57:32.28468+00:00
-- url     : https://prove2.me/theorems/f3aef5b1-b1fd-4c3b-a761-ef2796334e55
-- title:
--   Data Stream: class Table apply
-- statement:
--   The Data Stream construction uses the class Table apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L109-L111
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L109-L111

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.classTable_apply {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) (r s : Fin 2) :
    classTable C j r s = ∑ b, (∑ a, sel j r a * C a b) * sel j s b := by sorry
