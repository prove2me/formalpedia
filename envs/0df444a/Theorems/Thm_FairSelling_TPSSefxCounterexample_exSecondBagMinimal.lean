-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exSecondBagMinimal
-- name    : FairSelling.TPSSefxCounterexample.exSecondBagMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:39:00.649388+00:00
-- url     : https://prove2.me/theorems/71410f18-00c3-4d7e-ae4f-61bec45133b5
-- title:
--   TPSSefx Counterexample: ex Second Bag Minimal
-- statement:
--   The second bag `{g₂, g₃}` is worth `24` to each agent, and dropping either of its goods
--   leaves it below the threshold: it too is a minimal bag.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L159-L171
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L159-L171

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

theorem FairSelling.TPSSefxCounterexample.exSecondBagMinimal :
    vbarSum exv exp {2, 3} = 24 ∧
      vbarSum exv exp ({2, 3} \ {2}) < 20 ∧ vbarSum exv exp ({2, 3} \ {3}) < 20 := by sorry
