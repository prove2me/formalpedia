-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_soldSet
-- name    : FairSelling.PhaseTPS.PStage.toCStage_soldSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:20.482373+00:00
-- url     : https://prove2.me/theorems/ed346f8d-54eb-4a73-9859-99d54d526f70
-- title:
--   PStage: to CStage sold Set
-- statement:
--   The PStage construction uses the to CStage sold Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L222-L247
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L222-L247

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

theorem FairSelling.PhaseTPS.PStage.toCStage_soldSet (s : PStage G n) : (s.toCStage).soldSet = s.sold := by sorry
