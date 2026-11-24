-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_sum23
-- name    : FairSelling.TPSSefxCounterexample.sum23
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:24:03.548813+00:00
-- url     : https://prove2.me/theorems/a8a8add7-bace-4533-84cb-bb5dd18447a8
-- title:
--   TPSSefx Counterexample: sum23
-- statement:
--   A sum over the pair `{g₂, g₃}`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L106-L107
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L106-L107

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

theorem FairSelling.TPSSefxCounterexample.sum23 (f : Gd → ℝ) : ∑ x ∈ ({2, 3} : Finset Gd), f x = f 2 + f 3 := by sorry
