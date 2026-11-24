-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_saleLoss_nonneg
-- name    : FairSelling.ChargeTPS.saleLoss_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:50.902495+00:00
-- url     : https://prove2.me/theorems/8c0b98a2-5cc7-42df-a275-69ae492a326b
-- title:
--   Charge TPS: sale Loss nonneg
-- statement:
--   The Charge TPS construction uses the sale Loss nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L66-L67
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L66-L67

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.ChargeTPS.saleLoss_nonneg (w p : G → ℝ) (t : ℝ) (g : G) : 0 ≤ saleLoss w p t g := by sorry
