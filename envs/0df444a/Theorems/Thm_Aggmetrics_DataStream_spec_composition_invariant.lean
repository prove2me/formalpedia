-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_spec_composition_invariant
-- name    : Aggmetrics.DataStream.spec_composition_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:44.765712+00:00
-- url     : https://prove2.me/theorems/5e76a48b-483a-4648-a37c-4b3aab1c0368
-- title:
--   Data Stream: spec composition invariant
-- statement:
--   The specificity depends on the prior only through the composition of the other classes.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L209-L212
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L209-L212

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.spec_composition_invariant {m : ℕ} (π π' : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m)
    (h : ∀ k ∈ univ.erase j, π k / (1 - π j) = π' k / (1 - π' j)) :
    specFormula π c j = specFormula π' c j := by sorry
