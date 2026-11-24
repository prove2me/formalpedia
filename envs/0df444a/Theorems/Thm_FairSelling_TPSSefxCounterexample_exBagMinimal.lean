-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exBagMinimal
-- name    : FairSelling.TPSSefxCounterexample.exBagMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:38:55.315931+00:00
-- url     : https://prove2.me/theorems/3777886d-547e-4286-a603-a73b72951006
-- title:
--   TPSSefx Counterexample: ex Bag Minimal
-- statement:
--   **The bag `{g₀, g₁}` is a minimal bag**: it meets the threshold `20`, and dropping either of
--   its two goods leaves a bundle below the threshold.  So bag filling stops exactly there.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L146-L155
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L146-L155

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

theorem FairSelling.TPSSefxCounterexample.exBagMinimal :
    20 ≤ vbarSum exv exp {0, 1} ∧
      vbarSum exv exp ({0, 1} \ {0}) < 20 ∧ vbarSum exv exp ({0, 1} \ {1}) < 20 := by sorry
