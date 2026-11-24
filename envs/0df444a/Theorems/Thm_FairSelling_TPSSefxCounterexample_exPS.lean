-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exPS
-- name    : FairSelling.TPSSefxCounterexample.exPS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:46.204599+00:00
-- url     : https://prove2.me/theorems/1cdb85a4-f552-4a30-9d76-90ac8eea8988
-- title:
--   TPSSefx Counterexample: ex PS
-- statement:
--   The proportional share of each agent is `30`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L114-L116
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L114-L116

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

theorem FairSelling.TPSSefxCounterexample.exPS : PS 2 exv exp = 30 := by sorry
