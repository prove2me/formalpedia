-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_keepPart_subset
-- name    : FairSelling.EqualProceedsBagFilling.keepPart_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:25:39.125906+00:00
-- url     : https://prove2.me/theorems/929e8583-4bd9-4632-a36a-a7b0023026c8
-- title:
--   Equal Proceeds Bag Filling: keep Part subset
-- statement:
--   The Equal Proceeds Bag Filling construction uses the keep Part subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L77-L77
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L77-L77

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

theorem FairSelling.EqualProceedsBagFilling.keepPart_subset (B : Finset G) : keepPart vi p tk B ⊆ B := by sorry
