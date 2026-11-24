-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_saleLoss_le_vbar
-- name    : FairSelling.CfgTPS.saleLoss_le_vbar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:44.108797+00:00
-- url     : https://prove2.me/theorems/29646337-9883-4e1d-bf9a-067fd7bdd728
-- title:
--   Cfg TPS: sale Loss le vbar
-- statement:
--   The Cfg TPS construction uses the sale Loss le vbar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L278-L282
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L278-L282

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w : Fin n → G → ℝ} {p : G → ℝ} {req : Fin n → ℝ} {k0 : Fin n} {D : ℝ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.CfgTPS.saleLoss_le_vbar (t : ℝ) (u : G → ℝ) (g : G) :
    ChargeTPS.saleLoss u p t g ≤ vbar u p g - p g := by sorry
