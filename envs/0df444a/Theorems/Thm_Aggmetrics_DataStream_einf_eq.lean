-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_einf_eq
-- name    : Aggmetrics.DataStream.einf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:43.26492+00:00
-- url     : https://prove2.me/theorems/b10f94a6-3441-4c38-849e-e1b2138b9650
-- title:
--   Data Stream: einf eq
-- statement:
--   The Data Stream construction uses the einf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L123-L127
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L123-L127

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.einf_eq (ρ : ℕ → ℝ) (α : ℝ) :
    einf ρ α = (1 - α) * ∑' d : ℕ, α ^ d * ρ (d + 1) := by sorry
