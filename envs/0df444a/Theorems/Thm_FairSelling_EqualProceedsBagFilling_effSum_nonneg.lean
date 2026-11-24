-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_nonneg
-- name    : FairSelling.EqualProceedsBagFilling.effSum_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:05.892179+00:00
-- url     : https://prove2.me/theorems/12ce085d-3367-4726-babf-c75c86ce1369
-- title:
--   Equal Proceeds Bag Filling: eff Sum nonneg
-- statement:
--   The Equal Proceeds Bag Filling construction uses the eff Sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L89-L90
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L89-L90

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

theorem FairSelling.EqualProceedsBagFilling.effSum_nonneg (hp : ∀ g, 0 ≤ p g) (B : Finset G) : 0 ≤ effSum vi p tk B := by sorry
