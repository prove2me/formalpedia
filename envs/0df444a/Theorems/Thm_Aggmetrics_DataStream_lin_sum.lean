-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_lin_sum
-- name    : Aggmetrics.DataStream.lin_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:59:08.566051+00:00
-- url     : https://prove2.me/theorems/7e65cdb3-c27d-428a-a364-dc5ec2151160
-- title:
--   Data Stream: lin sum
-- statement:
--   The Data Stream construction uses the lin sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L168-L170
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L168-L170

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.lin_sum {m : ℕ} (a : Fin 4 → ℝ) (T : Fin m → Matrix (Fin 2) (Fin 2) ℝ) :
    lin a (∑ j, T j) = ∑ j, lin a (T j) := by sorry
