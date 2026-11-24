-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_Qc_le_of_gap
-- name    : FairSelling.CfgTPS.Qc_le_of_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:38.953843+00:00
-- url     : https://prove2.me/theorems/4254f228-0af8-42ab-a345-9c443ecab640
-- title:
--   Cfg TPS: Qc le of gap
-- statement:
--   An upper bound for the cash of a package.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L107-L109
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L107-L109

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

theorem FairSelling.CfgTPS.Qc_le_of_gap {S : Finset G} {c : ℝ} (hc : 0 ≤ c) (m : Fin n)
    (h : req m - vbarSum (w m) p S ≤ c) : Qc w p req k0 S ≤ c := by sorry
