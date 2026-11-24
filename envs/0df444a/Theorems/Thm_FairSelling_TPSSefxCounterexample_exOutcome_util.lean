-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exOutcome_util
-- name    : FairSelling.TPSSefxCounterexample.exOutcome_util
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:53.87766+00:00
-- url     : https://prove2.me/theorems/9f05a6e2-9c54-4182-8e0a-ad5969eb3f87
-- title:
--   TPSSefx Counterexample: ex Outcome util
-- statement:
--   Agent `0` gets `36` and agent `1` gets `24`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L190-L197
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L190-L197

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

theorem FairSelling.TPSSefxCounterexample.exOutcome_util : util exv exOutcome 0 = 36 ∧ util exv exOutcome 1 = 24 := by sorry
