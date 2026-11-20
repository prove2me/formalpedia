-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_covSum_succ
-- name    : Aggmetrics.DataStream.covSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:33.115225+00:00
-- url     : https://prove2.me/theorems/e704129c-27de-4842-b4c1-15e438eff24c
-- title:
--   Data Stream: cov Sum succ
-- statement:
--   Exact recursion for the double sum.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L73-L119
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L73-L119

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.covSum_succ (ρ : ℕ → ℝ) (hρ0 : ρ 0 = 1) (α : ℝ) (t : ℕ) :
    covSum ρ α (t + 1)
      = α ^ 2 * covSum ρ α t + 2 * α * (1 - α) * lagSum ρ α t + (1 - α) ^ 2 := by sorry
