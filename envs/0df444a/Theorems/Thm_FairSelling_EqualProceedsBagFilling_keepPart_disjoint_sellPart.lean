-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_keepPart_disjoint_sellPart
-- name    : FairSelling.EqualProceedsBagFilling.keepPart_disjoint_sellPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:28.495799+00:00
-- url     : https://prove2.me/theorems/2f3f4662-8b64-4ed3-bacc-24423f73dbd6
-- title:
--   Equal Proceeds Bag Filling: keep Part disjoint sell Part
-- statement:
--   The Equal Proceeds Bag Filling construction uses the keep Part disjoint sell Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L81-L84
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L81-L84

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

theorem FairSelling.EqualProceedsBagFilling.keepPart_disjoint_sellPart (B : Finset G) :
    Disjoint (keepPart vi p tk B) (sellPart vi p tk B) := by sorry
