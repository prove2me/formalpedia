-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_TPS_of_zero_val
-- name    : FairSelling.EqualProceedsBagFilling.TPS_of_zero_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:50.430051+00:00
-- url     : https://prove2.me/theorems/26fecb8c-e333-4cbf-9f27-357c8642f8a2
-- title:
--   Equal Proceeds Bag Filling: TPS of zero val
-- statement:
--   For a valuation that is identically zero, the truncated proportional share is just the
--   average price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L646-L659
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L646-L659

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

theorem FairSelling.EqualProceedsBagFilling.TPS_of_zero_val [Fintype G] (p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    TPS n (fun _ => (0 : ℝ)) p = (∑ g, p g) / n := by sorry
