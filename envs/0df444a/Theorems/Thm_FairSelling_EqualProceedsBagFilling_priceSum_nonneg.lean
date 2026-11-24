-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_priceSum_nonneg
-- name    : FairSelling.EqualProceedsBagFilling.priceSum_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:28.259879+00:00
-- url     : https://prove2.me/theorems/70ba94f6-5e90-4541-b8d3-14b7915eaba5
-- title:
--   Equal Proceeds Bag Filling: price Sum nonneg
-- statement:
--   The Equal Proceeds Bag Filling construction uses the price Sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L92-L93
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L92-L93

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

theorem FairSelling.EqualProceedsBagFilling.priceSum_nonneg (hp : ∀ g, 0 ≤ p g) (B : Finset G) : 0 ≤ priceSum p B := by sorry
