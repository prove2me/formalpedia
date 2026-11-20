-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selected_generatingAt
-- name    : DeletionCode.FiniteWalkRules.selected_generatingAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:58.094245+00:00
-- url     : https://prove2.me/theorems/645f52b1-cb94-440b-95ff-9b67d3bbee93
-- title:
--   Finite Walk Rules: selected generating At
-- statement:
--   The Finite Walk Rules construction uses the selected generating At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L138-L164
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L138-L164

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selected_generatingAt
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (hgen : GeneratingSelected (rationalPath p) S) :
    GeneratingAt (p 0) (selectedRules p S) := by sorry
