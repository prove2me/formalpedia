-- Prove2me | Theorems.Thm_DeletionCode_CanonicalIndex_group_filter_card
-- name    : DeletionCode.CanonicalIndex.group_filter_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:15:54.716974+00:00
-- url     : https://prove2.me/theorems/a3d84e3a-fbc4-495b-b442-a75c83301227
-- title:
--   Canonical Index: group filter card
-- statement:
--   The Canonical Index construction uses the group filter card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L71-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L71-L74

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators

theorem DeletionCode.CanonicalIndex.group_filter_card (t R : ℕ) (r : Fin R) :
    (Finset.univ.filter (fun b : Fin (2 * t * R) => group t R b = r)).card = 2 * t := by sorry
