-- Prove2me | Theorems.Thm_DeletionCode_CanonicalIndex_flat_bubble_spectrum
-- name    : DeletionCode.CanonicalIndex.flat_bubble_spectrum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:22:03.922086+00:00
-- url     : https://prove2.me/theorems/05b3c458-74b5-484f-89c5-4300d6c4c7f3
-- title:
--   Canonical Index: flat bubble spectrum
-- statement:
--   The Canonical Index construction uses the flat bubble spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L111-L114
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CanonicalIndex.lean#L111-L114

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators

theorem DeletionCode.CanonicalIndex.flat_bubble_spectrum {k : ℕ} (t R : ℕ)
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R)) :
    bubbleSpectrum (flatFamily t R words).family (windowLength k) b =
      bubbleSpectrum (pairFamily t R words).family (windowLength k) (indexEquiv t R b) := by sorry
