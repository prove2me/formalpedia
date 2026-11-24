-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_ptotal_nonneg
-- name    : FairSelling.PhaseTPS.ptotal_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:00:05.276446+00:00
-- url     : https://prove2.me/theorems/0eba7f46-d23e-46ae-ab40-2da4c41609e6
-- title:
--   Phase TPS: ptotal nonneg
-- statement:
--   The Phase TPS construction uses the ptotal nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L396-L398
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L396-L398

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.ptotal_nonneg (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : PStage G n}
    (hs : s.Good v p eps) : 0 ≤ s.total v p := by sorry
