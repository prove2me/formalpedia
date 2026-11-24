-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_Qc_claimed
-- name    : FairSelling.CfgTPS.Qc_claimed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:31.664244+00:00
-- url     : https://prove2.me/theorems/737c31aa-5708-49df-9eb3-492c485363e3
-- title:
--   Cfg TPS: Qc claimed
-- statement:
--   Somebody claims the package: the agent realizing the least gap.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L83-L90
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L83-L90

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)
omit [Fintype G] [DecidableEq G]

theorem FairSelling.CfgTPS.Qc_claimed (S : Finset G) : ∃ k, req k ≤ vbarSum (w k) p S + Qc w p req k0 S := by sorry
