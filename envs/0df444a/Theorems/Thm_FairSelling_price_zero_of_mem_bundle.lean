-- Prove2me | Theorems.Thm_FairSelling_price_zero_of_mem_bundle
-- name    : FairSelling.price_zero_of_mem_bundle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:34:03.65967+00:00
-- url     : https://prove2.me/theorems/dae418db-ac3a-469d-a99b-ce7f3234bdba
-- title:
--   Fair Selling: price zero of mem bundle
-- statement:
--   Goods allocated by a partition of the non-sellable goods have zero price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L212-L218
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L212-L218

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}

theorem FairSelling.price_zero_of_mem_bundle (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (j : Fin n) {g : G} (hg : g ∈ A j) :
    p g = 0 := by sorry
