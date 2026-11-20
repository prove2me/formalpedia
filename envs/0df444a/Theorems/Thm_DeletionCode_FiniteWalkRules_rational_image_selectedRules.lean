-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_rational_image_selectedRules
-- name    : DeletionCode.FiniteWalkRules.rational_image_selectedRules
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:42.105336+00:00
-- url     : https://prove2.me/theorems/515678d2-c3f5-4ab2-85e3-21e5d42d33d5
-- title:
--   Finite Walk Rules: rational image selected Rules
-- statement:
--   The Finite Walk Rules construction uses the rational image selected Rules property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L166-L176
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L166-L176

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.rational_image_selectedRules
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m)) :
    rational '' (↑(selectedRules p S) : Set _) =
      walkStep (rationalPath p) '' (↑S : Set (Fin m)) := by sorry
