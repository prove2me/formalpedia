-- Prove2me | Theorems.Thm_ConnesRigidity_exists_infinite_pairwise_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors
-- name    : ConnesRigidity.exists_infinite_pairwise_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/3e942051-f094-4662-a833-5f3e547dc0ec
-- title:
--   ConnesRigidity.exists_infinite_pairwise_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | ConnesRigidity | external Lean 4.33.1 validation; bundle SHA256 4ed9232ec35753a258ad689b720fbf6aae9317c7cf506b5797de1710cec6f4a3

import Mathlib
import Definitions.Def_ConnesRigidity
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
noncomputable section

theorem ConnesRigidity.exists_infinite_pairwise_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors :
    ∃ (Λ : ConnesRigidity.CountableDiscreteGroup.{0})
      (Γ : ℕ → ConnesRigidity.CountableDiscreteGroup.{0}),
      Group.FG Λ ∧
      (∀ n, Group.FG (Γ n)) ∧
      ConnesRigidity.IsICC Λ ∧
      (∀ n, ConnesRigidity.IsICC (Γ n)) ∧
      ConnesRigidity.HasKazhdanPropertyT Λ ∧
      (∀ n, ConnesRigidity.HasKazhdanPropertyT (Γ n)) ∧
      (∀ n, ConnesRigidity.TracialGroupFactorsIsomorphic (Γ n) Λ) ∧
      (∀ m n, ConnesRigidity.TracialGroupFactorsIsomorphic (Γ m) (Γ n)) ∧
      (∀ ⦃m n : ℕ⦄, m ≠ n →
        ¬ConnesRigidity.GroupsIsomorphic (Γ m) (Γ n)) ∧
      (∀ n, ¬ConnesRigidity.GroupsIsomorphic Λ (Γ n)) := by sorry
