-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selectedIndex_injective
-- name    : DeletionCode.FiniteWalkRules.selectedIndex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:35.689367+00:00
-- url     : https://prove2.me/theorems/667fc954-ad4d-40ca-8f4d-dc7de4cbac9e
-- title:
--   Finite Walk Rules: selected Index injective
-- statement:
--   The Finite Walk Rules construction uses the selected Index injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L85-L93
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L85-L93

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selectedIndex_injective
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    Function.Injective (selectedIndex p S) := by sorry
