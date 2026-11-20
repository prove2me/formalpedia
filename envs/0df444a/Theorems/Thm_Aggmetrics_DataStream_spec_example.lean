-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_spec_example
-- name    : Aggmetrics.DataStream.spec_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:08.910173+00:00
-- url     : https://prove2.me/theorems/642a4203-e4c0-431f-aad8-e4e8fd12568c
-- title:
--   Data Stream: spec example
-- statement:
--   Running example: each class is mistaken for the next one. A label shift between `B` and `C`
--   leaves the rows and the recall of `A` unchanged, and moves the specificity of `A` from `7/8` to
--   `13/16`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L230-L237
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L230-L237

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.spec_example :
    specFormula ![1 / 2, 1 / 4, 1 / 4]
      ![![3 / 4, 1 / 4, 0], ![0, 3 / 4, 1 / 4], ![1 / 4, 0, 3 / 4]] 0 = 7 / 8 ∧
    specFormula ![1 / 2, 1 / 8, 3 / 8]
      ![![3 / 4, 1 / 4, 0], ![0, 3 / 4, 1 / 4], ![1 / 4, 0, 3 / 4]] 0 = 13 / 16 := by sorry
