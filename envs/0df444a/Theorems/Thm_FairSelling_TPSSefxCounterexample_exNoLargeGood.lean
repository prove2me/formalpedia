-- Prove2me | Theorems.Thm_FairSelling_TPSSefxCounterexample_exNoLargeGood
-- name    : FairSelling.TPSSefxCounterexample.exNoLargeGood
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:38:08.623814+00:00
-- url     : https://prove2.me/theorems/3ac7b618-aabc-4d68-8769-e8077fb897d0
-- title:
--   TPSSefx Counterexample: ex No Large Good
-- statement:
--   No good is expensive enough or valuable enough to trigger the first two loops of the
--   algorithm: every price and every value is below the threshold `20`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L135-L136
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean#L135-L136

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

theorem FairSelling.TPSSefxCounterexample.exNoLargeGood : ∀ g : Gd, exp g < 20 ∧ exv g < 20 := by sorry
