-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_Qc_nonneg
-- name    : FairSelling.CfgTPS.Qc_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:23.0278+00:00
-- url     : https://prove2.me/theorems/e2e45ce0-23a1-4098-aff2-686ff2f8950b
-- title:
--   Cfg TPS: Qc nonneg
-- statement:
--   The Cfg TPS construction uses the Qc nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L79-L79
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L79-L79

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

theorem FairSelling.CfgTPS.Qc_nonneg (S : Finset G) : 0 ≤ Qc w p req k0 S := by sorry
