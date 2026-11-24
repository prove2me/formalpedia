-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_cash_add_saleLoss_le
-- name    : FairSelling.ChargeTPS.cash_add_saleLoss_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:15.865271+00:00
-- url     : https://prove2.me/theorems/5d2b6444-5101-48d8-9cd9-26f048292dae
-- title:
--   Charge TPS: cash add sale Loss le
-- statement:
--   **The single-good bound.**  Cash drawn from one single sold good, together with that good's
--   sale loss, never exceeds the truncation level.  This is what makes the *money* steps of
--   Algorithm 6 affordable: the agent that is charged with a sold good is one that draws its cash
--   from that very good.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L74-L80
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L74-L80

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

theorem FairSelling.ChargeTPS.cash_add_saleLoss_le (w p : G → ℝ) (t : ℝ) (g : G) (c : ℝ) (hc : c ≤ p g) (hct : c ≤ t) :
    c + saleLoss w p t g ≤ t := by sorry
