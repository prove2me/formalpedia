-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
-- name    : DeletionCode.FiniteWalkRules.selectedRules_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:13.438022+00:00
-- url     : https://prove2.me/theorems/3c5f4204-d327-47b7-8059-ac679ca78c4c
-- title:
--   Finite Walk Rules: selected Rules insert
-- statement:
--   The Finite Walk Rules construction uses the selected Rules insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L54-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L54-L58

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selectedRules_insert
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m) : selectedRules p (insert i S) = insert (step p i) (selectedRules p S) := by sorry
