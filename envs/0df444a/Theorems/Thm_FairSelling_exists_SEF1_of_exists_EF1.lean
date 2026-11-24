-- Prove2me | Theorems.Thm_FairSelling_exists_SEF1_of_exists_EF1
-- name    : FairSelling.exists_SEF1_of_exists_EF1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:16:10.516952+00:00
-- url     : https://prove2.me/theorems/f7a525c1-d2c0-4c5b-b998-0329371f0c1d
-- title:
--   Fair Selling: exists SEF1 of exists EF1
-- statement:
--   **Lemma 10, direction `EF1 ⟹ SEF1` (partial allocations).**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L268-L304
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L268-L304

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}

theorem FairSelling.exists_SEF1_of_exists_EF1 (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hEF1 : ∃ A : Fin n → Finset G, IsPartitionOf A (Finset.univ \ sellable) ∧ EF1alloc v A) :
    ∃ o : Outcome G n, o.Valid p ∧ o.AllocatesAll ∧ SEF1 v p o := by sorry
