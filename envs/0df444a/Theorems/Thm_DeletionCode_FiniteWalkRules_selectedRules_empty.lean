-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
-- name    : DeletionCode.FiniteWalkRules.selectedRules_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:28:59.686187+00:00
-- url     : https://prove2.me/theorems/7a6e5fe8-f896-43ed-8d28-ff9cb6d8992f
-- title:
--   Finite Walk Rules: selected Rules empty
-- statement:
--   The Finite Walk Rules construction uses the selected Rules empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L48-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L48-L52

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selectedRules_empty
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) :
    selectedRules p ∅ = ∅ := by sorry
