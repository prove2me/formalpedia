-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exBagValue
-- name    : FairSelling.TPSSefxCounterexample.exBagValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:45.75199+00:00
-- url     : https://prove2.me/theorems/906173f3-6b8c-4f72-9b25-6e6beac6aeb5
-- title:
--   TPSSefx Counterexample: ex Bag Value
-- statement:
--   The bag `{g₀, g₁}` is worth `36` to each agent.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L139-L142
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L139-L142

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

theorem FairSelling.TPSSefxCounterexample.exBagValue : vbarSum exv exp {0, 1} = 36 := by sorry
