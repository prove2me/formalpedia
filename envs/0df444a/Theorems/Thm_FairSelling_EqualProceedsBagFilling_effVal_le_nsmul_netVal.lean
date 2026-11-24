-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effVal_le_nsmul_netVal
-- name    : FairSelling.EqualProceedsBagFilling.effVal_le_nsmul_netVal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:17.529465+00:00
-- url     : https://prove2.me/theorems/432c50b7-e32e-4052-8a81-9190aed17f63
-- title:
--   Equal Proceeds Bag Filling: eff Val le nsmul net Val
-- statement:
--   `v'ᵢ(g) ≤ n · ṽᵢ(g)`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L118-L129
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L118-L129

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

theorem FairSelling.EqualProceedsBagFilling.effVal_le_nsmul_netVal (hv : ∀ g, 0 ≤ vi g) (ht : 0 ≤ tk)
    (hn : 0 < n) (g : G) : effVal vi p tk g ≤ (n : ℝ) * netVal n vi p tk g := by sorry
