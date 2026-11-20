-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRank_injOn
-- name    : DeletionCode.FiniteWalkRules.selectedRank_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:52.028266+00:00
-- url     : https://prove2.me/theorems/10d646d9-1c0e-43ab-9003-9863013250b5
-- title:
--   Finite Walk Rules: selected Rank inj On
-- statement:
--   The Finite Walk Rules construction uses the selected Rank inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L128-L136
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L128-L136

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selectedRank_injOn
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m))) :
    Set.InjOn (selectedRank p S) (↑(selectedRules p S) : Set _) := by sorry
