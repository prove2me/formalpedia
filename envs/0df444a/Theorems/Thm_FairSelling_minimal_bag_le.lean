-- Prove2me | Theorems.Thm_FairSelling_minimal_bag_le
-- name    : FairSelling.minimal_bag_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:12.423331+00:00
-- url     : https://prove2.me/theorems/3cc93c4c-5c29-4c4b-a282-afa6f8fc3db6
-- title:
--   Fair Selling: minimal bag le
-- statement:
--   A minimal bag is worth at most `τ + ε` when every element is worth at most `ε`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBagFilling.lean#L50-L60
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBagFilling.lean#L50-L60

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [DecidableEq G]

theorem FairSelling.minimal_bag_le {f : G → ℝ} {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε) {B : Finset G}
    (hsmall : ∀ g ∈ B, f g ≤ ε) (hge : τ ≤ ∑ g ∈ B, f g)
    (hmin : ∀ e ∈ B, ∑ g ∈ B.erase e, f g < τ) :
    ∑ g ∈ B, f g ≤ τ + ε := by sorry
