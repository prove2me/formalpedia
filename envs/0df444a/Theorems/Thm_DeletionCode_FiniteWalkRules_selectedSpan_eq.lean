-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selectedSpan_eq
-- name    : DeletionCode.FiniteWalkRules.selectedSpan_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:54.45507+00:00
-- url     : https://prove2.me/theorems/1fd2c7db-ccbc-451b-82ab-7c69b147aef2
-- title:
--   Finite Walk Rules: selected Span eq
-- statement:
--   The Finite Walk Rules construction uses the selected Span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L178-L183
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L178-L183

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selectedSpan_eq
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    selectedSpan (walkStep (rationalPath p)) S =
      Submodule.span ℚ (rational '' (↑(selectedRules p S) : Set _)) := by sorry
