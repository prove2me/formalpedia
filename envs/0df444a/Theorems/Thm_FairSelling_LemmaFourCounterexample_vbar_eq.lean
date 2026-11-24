-- Prove2me | Theorems.Thm_FairSelling_LemmaFourCounterexample_vbar_eq
-- name    : FairSelling.LemmaFourCounterexample.vbar_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:32.141341+00:00
-- url     : https://prove2.me/theorems/f8f3e41d-1278-4d52-b17e-529217e00e0e
-- title:
--   Lemma Four Counterexample: vbar eq
-- statement:
--   The Lemma Four Counterexample construction uses the vbar eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L66-L67
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L66-L67

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample

theorem FairSelling.LemmaFourCounterexample.vbar_eq (g : Fin 6) : vbar w p g = w g := by sorry
