-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selected_step_injOn
-- name    : DeletionCode.FiniteWalkRules.selected_step_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:26.329868+00:00
-- url     : https://prove2.me/theorems/83c10aa8-75a9-4450-861d-670698718fb5
-- title:
--   Finite Walk Rules: selected step inj On
-- statement:
--   The Finite Walk Rules construction uses the selected step inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L60-L68
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L60-L68

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selected_step_injOn
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Set.InjOn (step p) (↑S : Set (Fin m)) := by sorry
