-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_RunningExample_precision_example
-- name    : Aggmetrics.DataStream.RunningExample.precision_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:03:57.868382+00:00
-- url     : https://prove2.me/theorems/2ae267b8-3062-4882-9c00-d32a8936165a
-- title:
--   Running Example: precision example
-- statement:
--   Pooled precision `3/4`, weights `(1/4, 1/2, 1/4)`, per-class precisions `(1, 1, 0)`, the
--   denominator-weighted macro `3/4` (Theorem 1) and the unweighted macro `2/3`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean#L68-L114
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean#L68-L114

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamExample
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream Aggmetrics.DataStream.RunningExample

theorem Aggmetrics.DataStream.RunningExample.precision_example :
    measure aPrec bPrec (∑ j, classTable (winState 4 y p 8) j) = 3 / 4 ∧
    (omega bPrec (winState 4 y p 8) 0 = 1 / 4 ∧ omega bPrec (winState 4 y p 8) 1 = 1 / 2 ∧
      omega bPrec (winState 4 y p 8) 2 = 1 / 4) ∧
    (measure aPrec bPrec (classTable (winState 4 y p 8) 0) = 1 ∧
      measure aPrec bPrec (classTable (winState 4 y p 8) 1) = 1 ∧
      measure aPrec bPrec (classTable (winState 4 y p 8) 2) = 0) ∧
    (∑ j, omega bPrec (winState 4 y p 8) j * measure aPrec bPrec (classTable (winState 4 y p 8) j)
      = 3 / 4) ∧
    ((measure aPrec bPrec (classTable (winState 4 y p 8) 0)
      + measure aPrec bPrec (classTable (winState 4 y p 8) 1)
      + measure aPrec bPrec (classTable (winState 4 y p 8) 2)) / 3 = 2 / 3) := by sorry
