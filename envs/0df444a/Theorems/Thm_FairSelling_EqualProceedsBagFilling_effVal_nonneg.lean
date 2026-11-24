-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effVal_nonneg
-- name    : FairSelling.EqualProceedsBagFilling.effVal_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:41.697802+00:00
-- url     : https://prove2.me/theorems/0267e56c-9b24-44be-bda9-95c90be9b663
-- title:
--   Equal Proceeds Bag Filling: eff Val nonneg
-- statement:
--   The Equal Proceeds Bag Filling construction uses the eff Val nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L86-L87
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L86-L87

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

theorem FairSelling.EqualProceedsBagFilling.effVal_nonneg (hp : ∀ g, 0 ≤ p g) (g : G) : 0 ≤ effVal vi p tk g := by sorry
