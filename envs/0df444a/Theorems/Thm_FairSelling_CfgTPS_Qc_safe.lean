-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_Qc_safe
-- name    : FairSelling.CfgTPS.Qc_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:38.034329+00:00
-- url     : https://prove2.me/theorems/1d36e614-34f6-413b-9c71-d4210b1251c0
-- title:
--   Cfg TPS: Qc safe
-- statement:
--   A package that carries money is envied by nobody.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L94-L103
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L94-L103

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

theorem FairSelling.CfgTPS.Qc_safe {S : Finset G} (h : 0 < Qc w p req k0 S) (m : Fin n) :
    vbarSum (w m) p S + Qc w p req k0 S ≤ req m := by sorry
