-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exOutcome_TPS
-- name    : FairSelling.TPSSefxCounterexample.exOutcome_TPS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:39:33.573555+00:00
-- url     : https://prove2.me/theorems/20354d38-4cf0-45db-be87-ac5bea06785a
-- title:
--   TPSSefx Counterexample: ex Outcome TPS
-- statement:
--   **The output does meet the share guarantee**: both agents are above `(2/3)·TPS = 20`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L200-L208
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L200-L208

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

theorem FairSelling.TPSSefxCounterexample.exOutcome_TPS :
    ∀ i, ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 (exV i) exp ≤ util (exV i) exOutcome i := by sorry
