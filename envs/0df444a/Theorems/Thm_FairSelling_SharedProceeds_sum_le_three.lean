-- Prove2me | Theorems.Thm_FairSelling_SharedProceeds_sum_le_three
-- name    : FairSelling.SharedProceeds.sum_le_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:39.671676+00:00
-- url     : https://prove2.me/theorems/53c0e020-552e-46db-ad6e-9853f4401492
-- title:
--   Shared Proceeds: sum le three
-- statement:
--   The value of any bundle avoiding the big good is at most `3`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L80-L88
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L80-L88

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds

theorem FairSelling.SharedProceeds.sum_le_three {A : Finset (Fin 4)} (hA : (0 : Fin 4) ∉ A) : ∑ g ∈ A, sv g ≤ 3 := by sorry
