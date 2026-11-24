-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_netSum_split
-- name    : FairSelling.EqualProceedsBagFilling.netSum_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:32.517789+00:00
-- url     : https://prove2.me/theorems/6646855c-9374-4000-8011-68f6fc51ece4
-- title:
--   Equal Proceeds Bag Filling: net Sum split
-- statement:
--   The net value of a bundle splits into the effective value of the kept part plus `1/n` of the
--   price of the sold part.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L153-L168
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L153-L168

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

theorem FairSelling.EqualProceedsBagFilling.netSum_split (B : Finset G) :
    netSum n vi p tk B
      = effSum vi p tk (keepPart vi p tk B) + priceSum p (sellPart vi p tk B) / n := by sorry
