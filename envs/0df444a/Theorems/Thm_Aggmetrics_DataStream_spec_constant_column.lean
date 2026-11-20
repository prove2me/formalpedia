-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_spec_constant_column
-- name    : Aggmetrics.DataStream.spec_constant_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:41.242818+00:00
-- url     : https://prove2.me/theorems/1c21017c-9088-41b4-a0e7-69d2d220f45f
-- title:
--   Data Stream: spec constant column
-- statement:
--   If column `j` of the confusion matrix is constant over `k ≠ j`, the specificity is `1 - γ`
--   for every prior.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L216-L225
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L216-L225

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.spec_constant_column {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m) (γ : ℝ)
    (hπ : ∑ k, π k = 1) (hj : π j ≠ 1) (hcol : ∀ k, k ≠ j → c k j = γ) :
    specFormula π c j = 1 - γ := by sorry
