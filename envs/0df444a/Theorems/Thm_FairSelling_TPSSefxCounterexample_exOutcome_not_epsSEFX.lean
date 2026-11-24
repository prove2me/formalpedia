-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exOutcome_not_epsSEFX
-- name    : FairSelling.TPSSefxCounterexample.exOutcome_not_epsSEFX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:59.169808+00:00
-- url     : https://prove2.me/theorems/56d60b87-a5b0-482b-acdf-8da24eedc2c7
-- title:
--   TPSSefx Counterexample: ex Outcome not eps SEFX
-- statement:
--   **But agent `1` envies agent `0` outright.**  Agent `0` holds money, so Definition 4 asks
--   for the full envy-free condition; agent `1`'s bundle is worth `24` to it, while agent `0`'s is
--   worth `36`.  The outcome is therefore not `ε`-SEFX for any `ε` (the full envy-free condition
--   towards a money-holding agent carries no `ε`), in particular not SEFX.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L214-L227
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L214-L227

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

theorem FairSelling.TPSSefxCounterexample.exOutcome_not_epsSEFX (eps : ℝ) : ¬ epsSEFX exV exp eps exOutcome := by sorry
