-- Prove2me | Theorems.Thm_DeletionCode_CanonicalIndex_group_sum
-- name    : DeletionCode.CanonicalIndex.group_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:21:16.173755+00:00
-- url     : https://prove2.me/theorems/c0ced703-c0a2-4d6e-b55a-e6e3cf799fb2
-- title:
--   Canonical Index: group sum
-- statement:
--   Sums over one flat-index group are exactly sums over its within-rule indices.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L77-L101
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L77-L101

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators

theorem DeletionCode.CanonicalIndex.group_sum {A : Type*} [AddCommMonoid A] (t R : ℕ) (r : Fin R)
    (f : Fin (2 * t * R) → A) :
    (∑ b ∈ Finset.univ.filter (fun b => group t R b = r), f b) =
      ∑ j : Fin (2 * t), f ((indexEquiv t R).symm (r, j)) := by sorry
