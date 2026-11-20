-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_novelty_transfer
-- name    : DeletionCode.FiniteWalkRules.novelty_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:45.976503+00:00
-- url     : https://prove2.me/theorems/1f6763d5-de1c-457d-bede-f646455afdbd
-- title:
--   Finite Walk Rules: novelty transfer
-- statement:
--   The Finite Walk Rules construction uses the novelty transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L185-L200
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L185-L200

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.novelty_transfer
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m)
    (hnew : ¬ SignedMember (walkStep (rationalPath p)) S (walkStep (rationalPath p) i)) :
    ∀ u ∈ selectedRules p S, step p i ≠ u ∧ step p i ≠ -u := by sorry
