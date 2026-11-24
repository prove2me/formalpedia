-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_sellPart_subset
-- name    : FairSelling.EqualProceedsBagFilling.sellPart_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:25:40.063551+00:00
-- url     : https://prove2.me/theorems/4cbaed1a-ac8a-4508-ab1c-cb8ca02d1875
-- title:
--   Equal Proceeds Bag Filling: sell Part subset
-- statement:
--   The Equal Proceeds Bag Filling construction uses the sell Part subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L79-L79
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L79-L79

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

theorem FairSelling.EqualProceedsBagFilling.sellPart_subset (B : Finset G) : sellPart vi p tk B ⊆ B := by sorry
