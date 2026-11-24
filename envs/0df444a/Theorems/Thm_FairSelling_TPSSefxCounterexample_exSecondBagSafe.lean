-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exSecondBagSafe
-- name    : FairSelling.TPSSefxCounterexample.exSecondBagSafe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:40:01.246614+00:00
-- url     : https://prove2.me/theorems/8dca13e9-11cb-4091-9f54-7f077b7d6c46
-- title:
--   TPSSefx Counterexample: ex Second Bag Safe
-- statement:
--   Agent `0`, holding the first bag, does not `ε`-SEFX-envy the second bag: the manuscript's
--   stealing test does not fire, so the run really is a run of Algorithm 6.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L235-L242
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L235-L242

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

theorem FairSelling.TPSSefxCounterexample.exSecondBagSafe :
    vbarSum (exV 0) exp (exOutcome.kept 1) + exOutcome.money 1
      ≤ vbarSum (exV 0) exp (exOutcome.kept 0) + exOutcome.money 0 := by sorry
