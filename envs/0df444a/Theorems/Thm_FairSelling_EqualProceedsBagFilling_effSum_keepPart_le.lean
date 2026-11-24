-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_keepPart_le
-- name    : FairSelling.EqualProceedsBagFilling.effSum_keepPart_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:41.916879+00:00
-- url     : https://prove2.me/theorems/6a2abe83-2d07-46be-be7a-76687676242a
-- title:
--   Equal Proceeds Bag Filling: eff Sum keep Part le
-- statement:
--   On the kept part, the effective value is bounded by the true value.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L171-L176
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L171-L176

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}

theorem FairSelling.EqualProceedsBagFilling.effSum_keepPart_le (B : Finset G) :
    effSum vi p tk (keepPart vi p tk B) ≤ ∑ g ∈ keepPart vi p tk B, vi g := by sorry
