-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_split
-- name    : FairSelling.EqualProceedsBagFilling.effSum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:28.091096+00:00
-- url     : https://prove2.me/theorems/2e16bbfd-7660-4907-8fd1-ea319e109ab8
-- title:
--   Equal Proceeds Bag Filling: eff Sum split
-- statement:
--   The effective value of a bundle splits into the effective value of the kept part plus the
--   price of the sold part.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L140-L149
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L140-L149

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

theorem FairSelling.EqualProceedsBagFilling.effSum_split (B : Finset G) :
    effSum vi p tk B = effSum vi p tk (keepPart vi p tk B) + priceSum p (sellPart vi p tk B) := by sorry
