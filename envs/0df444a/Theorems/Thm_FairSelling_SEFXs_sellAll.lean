-- Prove2me | Theorems.Thm_FairSelling_SEFXs_sellAll
-- name    : FairSelling.SEFXs_sellAll
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:32.737137+00:00
-- url     : https://prove2.me/theorems/75ddba6d-6f26-4a87-a4df-0aa34c01e999
-- title:
--   Fair Selling: SEFXs sell All
-- statement:
--   **Lemma 10, direction `EFX ⟹ SEFX` (partial allocations).**  Selling every sellable good and
--   allocating the non-sellable goods according to an `EFX` allocation yields a valid outcome that
--   allocates or sells every good and is `SEFXs` (hence `SEFX`).  The proceeds are not distributed,
--   so this is a partial allocation.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L224-L256
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L224-L256

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}

theorem FairSelling.SEFXs_sellAll (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (hEFX : EFXalloc v A) :
    (sellAllOutcome sellable A (fun _ => 0)).Valid p ∧
      (sellAllOutcome sellable A (fun _ => 0)).AllocatesAll ∧
      SEFXs v p (sellAllOutcome sellable A (fun _ => 0)) := by sorry
