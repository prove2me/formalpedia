-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_sum01
-- name    : FairSelling.TPSSefxCounterexample.sum01
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:37.519369+00:00
-- url     : https://prove2.me/theorems/efec11bc-05bc-497b-b992-18b304d8d58a
-- title:
--   TPSSefx Counterexample: sum01
-- statement:
--   A sum over the pair `{g₀, g₁}`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L110-L111
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L110-L111

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

theorem FairSelling.TPSSefxCounterexample.sum01 (f : Gd → ℝ) : ∑ x ∈ ({0, 1} : Finset Gd), f x = f 0 + f 1 := by sorry
