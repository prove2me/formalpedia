-- Prove2me | Theorems.Thm_DeletionCode_CanonicalIndex_every_family_is_flattened
-- name    : DeletionCode.CanonicalIndex.every_family_is_flattened
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:15:54.490224+00:00
-- url     : https://prove2.me/theorems/5e2d8402-e8c4-414a-ba3c-c6a392c09cc9
-- title:
--   Canonical Index: every family is flattened
-- statement:
--   The Canonical Index construction uses the every family is flattened property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L52-L54
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L52-L54

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators

theorem DeletionCode.CanonicalIndex.every_family_is_flattened {α : Type*} (t R : ℕ) (family : Fin (2 * t * R) → α) :
    ∃ words : Fin R → Fin (2 * t) → α, flatten t R words = family := by sorry
