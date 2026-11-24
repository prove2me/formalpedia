-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exOutcome_not_SEFX
-- name    : FairSelling.TPSSefxCounterexample.exOutcome_not_SEFX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:39:35.452816+00:00
-- url     : https://prove2.me/theorems/78768063-6d9b-4992-8ce3-e74b2b58b933
-- title:
--   TPSSefx Counterexample: ex Outcome not SEFX
-- statement:
--   The TPSSefx Counterexample construction uses the ex Outcome not SEFX property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L229-L231
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L229-L231

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample

theorem FairSelling.TPSSefxCounterexample.exOutcome_not_SEFX : ¬ SEFX exV exp exOutcome := by sorry
