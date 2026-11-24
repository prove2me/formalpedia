-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effVal_le_of_price_le
-- name    : FairSelling.EqualProceedsBagFilling.effVal_le_of_price_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:11.236559+00:00
-- url     : https://prove2.me/theorems/0c99439e-6027-4f99-af43-8636dabd8513
-- title:
--   Equal Proceeds Bag Filling: eff Val le of price le
-- statement:
--   If a good is not more expensive than the target, its effective value is at most the
--   target.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L114-L115
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L114-L115

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

theorem FairSelling.EqualProceedsBagFilling.effVal_le_of_price_le (h : p g ≤ tk) : effVal vi p tk g ≤ tk := by sorry
