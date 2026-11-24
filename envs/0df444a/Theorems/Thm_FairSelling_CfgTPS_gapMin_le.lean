-- Prove2me | Theorems.Thm_FairSelling_CfgTPS_gapMin_le
-- name    : FairSelling.CfgTPS.gapMin_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:28:13.114359+00:00
-- url     : https://prove2.me/theorems/1fa1d2da-515c-43f0-b5f4-f3ef4aaf5e8e
-- title:
--   Cfg TPS: gap Min le
-- statement:
--   The Cfg TPS construction uses the gap Min le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L74-L76
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean#L74-L76

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

theorem FairSelling.CfgTPS.gapMin_le (S : Finset G) (m : Fin n) :
    gapMin w p req k0 S ≤ req m - vbarSum (w m) p S := by sorry
