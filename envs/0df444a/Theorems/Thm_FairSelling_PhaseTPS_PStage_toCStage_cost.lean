-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cost
-- name    : FairSelling.PhaseTPS.PStage.toCStage_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:59:13.211129+00:00
-- url     : https://prove2.me/theorems/3c8941a8-eca6-4630-8b21-bcf78b21a776
-- title:
--   PStage: to CStage cost
-- statement:
--   The PStage construction uses the to CStage cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L260-L283
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L260-L283

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

theorem FairSelling.PhaseTPS.PStage.toCStage_cost {s : PStage G n} (hs : s.Good v p eps) (i j : Fin n) (hj : j ∉ s.served) :
    (s.toCStage).cost v p i j = s.cost v p i j := by sorry
