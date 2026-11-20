-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selected_independent
-- name    : DeletionCode.FiniteWalkRules.selected_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:49.341209+00:00
-- url     : https://prove2.me/theorems/362e9502-c841-49f8-b3a7-2434f714602e
-- title:
--   Finite Walk Rules: selected independent
-- statement:
--   The Finite Walk Rules construction uses the selected independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L103-L112
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L103-L112

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selected_independent
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Independent (selectedRules p S) := by sorry
