-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_Qc_empty_le
-- name    : FairSelling.CfgTPS.Qc_empty_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:19:29.373375+00:00
-- url     : https://prove2.me/theorems/41c261f9-2192-4b02-b5f9-0fe820ba822e
-- title:
--   Cfg TPS: Qc empty le
-- statement:
--   The Cfg TPS construction uses the Qc empty le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L285-L289
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L285-L289

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

theorem FairSelling.CfgTPS.Qc_empty_le (hreq0 : ∀ m, 0 ≤ req m) (m : Fin n) : Qc w p req k0 ∅ ≤ req m := by sorry
