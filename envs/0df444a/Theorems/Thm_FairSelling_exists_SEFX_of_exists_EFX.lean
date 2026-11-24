-- Prove2me | Theorems.Thm_FairSelling_exists_SEFX_of_exists_EFX
-- name    : FairSelling.exists_SEFX_of_exists_EFX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:16:11.128025+00:00
-- url     : https://prove2.me/theorems/86f7803e-b69f-47e0-a6e7-54e6eb0d4857
-- title:
--   Fair Selling: exists SEFX of exists EFX
-- statement:
--   **Lemma 10, direction `EFX ⟹ SEFX` (partial allocations), packaged form.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L259-L265
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L259-L265

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}

theorem FairSelling.exists_SEFX_of_exists_EFX (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hEFX : ∃ A : Fin n → Finset G, IsPartitionOf A (Finset.univ \ sellable) ∧ EFXalloc v A) :
    ∃ o : Outcome G n, o.Valid p ∧ o.AllocatesAll ∧ SEFX v p o := by sorry
