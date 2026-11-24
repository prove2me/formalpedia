-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effVal_le_add
-- name    : FairSelling.EqualProceedsBagFilling.effVal_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:02.835323+00:00
-- url     : https://prove2.me/theorems/28cb6eee-17b6-42da-9d79-5711bb5477ab
-- title:
--   Equal Proceeds Bag Filling: eff Val le add
-- statement:
--   `v'ᵢ(g) ≤ p(g) + tᵢ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L107-L110
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L107-L110

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

theorem FairSelling.EqualProceedsBagFilling.effVal_le_add (hp : ∀ g, 0 ≤ p g) (ht : 0 ≤ tk) (g : G) :
    effVal vi p tk g ≤ p g + tk := by sorry
