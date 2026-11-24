-- Prove2me | Theorems.Thm_FairSelling_exists_bags
-- name    : FairSelling.exists_bags
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:13:05.948106+00:00
-- url     : https://prove2.me/theorems/f60bb175-aa7a-474e-840c-b86720aca015
-- title:
--   Fair Selling: exists bags
-- statement:
--   **Bag filling.**  If every good of `A` is worth at most `ε` and `A` is worth at least
--   `k · (τ + ε)`, then `A` contains `k` pairwise disjoint bags, each worth at least `τ` and at most
--   `τ + ε`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBagFilling.lean#L65-L126
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBagFilling.lean#L65-L126

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [DecidableEq G]

theorem FairSelling.exists_bags (f : G → ℝ) (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    ∀ (k : ℕ) (A : Finset G), (∀ g ∈ A, f g ≤ ε) → (k : ℝ) * (τ + ε) ≤ ∑ g ∈ A, f g →
      ∃ B : Fin k → Finset G, (∀ j, B j ⊆ A) ∧
        (∀ j j', j ≠ j' → Disjoint (B j) (B j')) ∧
        (∀ j, τ ≤ ∑ g ∈ B j, f g) ∧ (∀ j, ∑ g ∈ B j, f g ≤ τ + ε) := by sorry
