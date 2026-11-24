-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exThreshold
-- name    : FairSelling.TPSSefxCounterexample.exThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:26.834862+00:00
-- url     : https://prove2.me/theorems/0395ae7e-fcbb-438c-8efe-0b59a686367f
-- title:
--   TPSSefx Counterexample: ex Threshold
-- statement:
--   The threshold used by the algorithm: `τ = (2/3)·TPS = 20`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L128-L129
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L128-L129

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

theorem FairSelling.TPSSefxCounterexample.exThreshold : ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp = 20 := by sorry
