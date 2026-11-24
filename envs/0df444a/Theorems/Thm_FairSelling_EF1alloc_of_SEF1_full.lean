-- Prove2me | Theorems.Thm_FairSelling_EF1alloc_of_SEF1_full
-- name    : FairSelling.EF1alloc_of_SEF1_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:28.77764+00:00
-- url     : https://prove2.me/theorems/466dc24c-d8fe-4bb6-ab36-296cae1375be
-- title:
--   Fair Selling: EF1alloc of SEF1 full
-- statement:
--   If no good is sellable, a full `SEF1` allocation *is* an `EF1` allocation.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L156-L188
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L156-L188

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.EF1alloc_of_SEF1_full (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (p : G → ℝ)
    (hp : ∀ g, p g = 0) (o : Outcome G n) (hfull : o.Full p ∅) (hsef1 : SEF1 v p o) :
    IsPartitionOf o.kept Finset.univ ∧ EF1alloc v o.kept := by sorry
