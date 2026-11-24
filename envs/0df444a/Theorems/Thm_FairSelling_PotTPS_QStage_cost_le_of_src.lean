-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_cost_le_of_src
-- name    : FairSelling.PotTPS.QStage.cost_le_of_src
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:50:51.824116+00:00
-- url     : https://prove2.me/theorems/6d9132bb-931a-4a47-bc2e-9c586e77d715
-- title:
--   QStage: cost le of src
-- statement:
--   **The cost of a slice holder.**  An agent whose package is a slice of the proceeds of a cut
--   good costs every unserved agent at most `2τ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L309-L325
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L309-L325

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem FairSelling.PotTPS.QStage.cost_le_of_src (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    {i : Fin n} (hi : s.src i ≠ ∅) {j : Fin n}
    (hcash : s.cash i ≤ GeneralTPS.thr v p j) :
    s.cost v p i j ≤ 2 * GeneralTPS.thr v p j := by sorry
