-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_pot_of_pool
-- name    : FairSelling.PotTPS.QStage.pot_of_pool
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:42:51.098746+00:00
-- url     : https://prove2.me/theorems/b7578a1a-31ba-4dce-b754-40ef62aa7c7a
-- title:
--   QStage: pot of pool
-- statement:
--   The pot of a good that is still in the pool is its whole price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L292-L297
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L292-L297

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

theorem FairSelling.PotTPS.QStage.pot_of_pool {s : QStage G n} {g : G} (hg : g ∈ s.pool) : s.pot p g = p g := by sorry
