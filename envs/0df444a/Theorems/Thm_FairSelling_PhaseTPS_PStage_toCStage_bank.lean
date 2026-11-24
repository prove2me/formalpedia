-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
-- name    : FairSelling.PhaseTPS.PStage.toCStage_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:44.704814+00:00
-- url     : https://prove2.me/theorems/98caaa31-ff21-4de0-b50b-107b3cd1da2a
-- title:
--   PStage: to CStage bank
-- statement:
--   The PStage construction uses the to CStage bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L210-L210
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L210-L210

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [Fintype G]

theorem FairSelling.PhaseTPS.PStage.toCStage_bank (s : PStage G n) : (s.toCStage).bank = s.bank := by sorry

attribute [defeq] FairSelling.PhaseTPS.PStage.toCStage_bank
