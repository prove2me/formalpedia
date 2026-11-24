-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_le_nsmul_netSum
-- name    : FairSelling.EqualProceedsBagFilling.effSum_le_nsmul_netSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:19.835455+00:00
-- url     : https://prove2.me/theorems/465be8cc-374e-43ba-8eed-434b20de9516
-- title:
--   Equal Proceeds Bag Filling: eff Sum le nsmul net Sum
-- statement:
--   The Equal Proceeds Bag Filling construction uses the eff Sum le nsmul net Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L131-L136
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L131-L136

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

theorem FairSelling.EqualProceedsBagFilling.effSum_le_nsmul_netSum (hv : ∀ g, 0 ≤ vi g) (ht : 0 ≤ tk)
    (hn : 0 < n) (B : Finset G) :
    effSum vi p tk B ≤ (n : ℝ) * netSum n vi p tk B := by sorry
