-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selectedIndex_spec
-- name    : DeletionCode.FiniteWalkRules.selectedIndex_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:12.161176+00:00
-- url     : https://prove2.me/theorems/91c64479-9202-4c6d-b545-b63553e5ce2d
-- title:
--   Finite Walk Rules: selected Index spec
-- statement:
--   The Finite Walk Rules construction uses the selected Index spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L80-L83
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L80-L83

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selectedIndex_spec
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : step p (selectedIndex p S u).val = u.val := by sorry
