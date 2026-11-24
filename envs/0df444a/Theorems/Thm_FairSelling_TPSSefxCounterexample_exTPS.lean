-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exTPS
-- name    : FairSelling.TPSSefxCounterexample.exTPS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:49.418092+00:00
-- url     : https://prove2.me/theorems/1486129b-ae55-4dea-865c-9e1f765bba31
-- title:
--   TPSSefx Counterexample: ex TPS
-- statement:
--   **The truncated proportional share of each agent is `30`.**  Every value is at most `19`,
--   and the truncated proportional map already exceeds `19` there, so the share equals the
--   proportional share (the `k = 1` case of the manuscript's computation).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L121-L125
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L121-L125

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

theorem FairSelling.TPSSefxCounterexample.exTPS : TPS 2 exv exp = 30 := by sorry
