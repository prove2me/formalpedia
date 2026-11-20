-- Prove2me | Theorems.Thm_DeletionCode_CanonicalIndex_group_fiber_card
-- name    : DeletionCode.CanonicalIndex.group_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:21:15.4282+00:00
-- url     : https://prove2.me/theorems/bbfb44a1-c824-48b8-b3f9-039cfdc0fa60
-- title:
--   Canonical Index: group fiber card
-- statement:
--   The Canonical Index construction uses the group fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L67-L69
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L67-L69

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators

theorem DeletionCode.CanonicalIndex.group_fiber_card (t R : ℕ) (r : Fin R) :
    Fintype.card {b : Fin (2 * t * R) // group t R b = r} = 2 * t := by sorry
