-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_macroExclude_indep
-- name    : Aggmetrics.DataStream.macroExclude_indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:18:11.819185+00:00
-- url     : https://prove2.me/theorems/abc8bd71-fa49-46d3-bcd4-57f170a04fd7
-- title:
--   Data Stream: macro Exclude indep
-- statement:
--   The macro value of `exclude` does not depend on the values of unsupported classes.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L320-L324
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L320-L324

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.macroExclude_indep {m : ℕ} (u : Fin m → Bool) (v v' : Fin m → ℝ)
    (h : ∀ j, u j = true → v j = v' j) : macroExclude u v = macroExclude u v' := by sorry
