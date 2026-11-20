-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_lin_nonneg
-- name    : Aggmetrics.DataStream.lin_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:58:58.541421+00:00
-- url     : https://prove2.me/theorems/de508e67-4f6c-4d5c-917f-d3666ce9e212
-- title:
--   Data Stream: lin nonneg
-- statement:
--   The Data Stream construction uses the lin nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L172-L177
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L172-L177

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.lin_nonneg {a : Fin 4 → ℝ} (ha : ∀ i, 0 ≤ a i) {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hT : ∀ r s, 0 ≤ T r s) : 0 ≤ lin a T := by sorry
