-- Prove2me | Theorems.Thm_FairSelling_exists_minimal_subset_sum
-- name    : FairSelling.exists_minimal_subset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:14.751542+00:00
-- url     : https://prove2.me/theorems/af55b8ac-a7f2-4f51-98a6-9599c5fd622f
-- title:
--   Fair Selling: exists minimal subset sum
-- statement:
--   From any finite set whose total `f`-value reaches `τ`, one can pass to a subset that still
--   reaches `τ` but drops below `τ` as soon as any single element is removed.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBagFilling.lean#L35-L47
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBagFilling.lean#L35-L47

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [DecidableEq G]

theorem FairSelling.exists_minimal_subset_sum (f : G → ℝ) (τ : ℝ) :
    ∀ A : Finset G, τ ≤ ∑ g ∈ A, f g →
      ∃ B ⊆ A, τ ≤ ∑ g ∈ B, f g ∧ ∀ e ∈ B, ∑ g ∈ B.erase e, f g < τ := by sorry
