-- Prove2me | Theorems.Thm_DeletionCode_CanonicalIndex_rulesOf_flatten
-- name    : DeletionCode.CanonicalIndex.rulesOf_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:04.522238+00:00
-- url     : https://prove2.me/theorems/b3991bee-32d7-48b2-bd4c-55fde73a2b3d
-- title:
--   Canonical Index: rules Of flatten
-- statement:
--   The flattened decoder output determines precisely the set of the R per-rule sums.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L131-L139
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L131-L139

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators

theorem DeletionCode.CanonicalIndex.rulesOf_flatten {k : ℕ} (t R : ℕ) (words : Fin R → Fin (2 * t) → BubbleWord k) :
    rulesOfFamily (flatFamily t R words) (group t R) =
      Finset.univ.image (fun r : Fin R => fun g =>
        ∑ j : Fin (2 * t), bubbleSpectrum (pairFamily t R words).family (windowLength k) (r, j) g) := by sorry
