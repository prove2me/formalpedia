-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_fade_Ico_sum
-- name    : Aggmetrics.DataStream.fade_Ico_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:33.619718+00:00
-- url     : https://prove2.me/theorems/b6b4a36a-3505-4173-ac9b-004fa51838b6
-- title:
--   Data Stream: fade Ico sum
-- statement:
--   The Data Stream construction uses the fade Ico sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L253-L259
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L253-L259

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.fade_Ico_sum {α : ℝ} (s N : ℕ) (hsN : s ≤ N) :
    ∑ j ∈ Ico s N, (1 - α) * α ^ j = α ^ s - α ^ N := by sorry
