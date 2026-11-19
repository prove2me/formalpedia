-- Prove2me | Theorems.Thm_DeletionCode_CanonicalIndex_flat_rule_spectrum
-- name    : DeletionCode.CanonicalIndex.flat_rule_spectrum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:18:00.009445+00:00
-- url     : https://prove2.me/theorems/7fc55201-5248-4194-8616-fa81e0ad8bde
-- title:
--   Canonical Index: flat rule spectrum
-- statement:
--   The Canonical Index construction uses the flat rule spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L116-L128
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L116-L128

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators

theorem DeletionCode.CanonicalIndex.flat_rule_spectrum {k : ℕ} (t R : ℕ)
    (words : Fin R → Fin (2 * t) → BubbleWord k) (r : Fin R) :
    ruleSpectrum (flatFamily t R words).family (windowLength k) (groupBubbles (group t R) r) =
      fun g => ∑ j : Fin (2 * t), bubbleSpectrum (pairFamily t R words).family
        (windowLength k) (r, j) g := by sorry
