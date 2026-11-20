-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRank_step
-- name    : DeletionCode.FiniteWalkRules.selectedRank_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:22.754436+00:00
-- url     : https://prove2.me/theorems/a6f86b52-e532-427e-9829-b0bc08d6295e
-- title:
--   Finite Walk Rules: selected Rank step
-- statement:
--   The Finite Walk Rules construction uses the selected Rank step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L120-L126
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L120-L126

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.selectedRank_step
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn ℚ (walkStep (rationalPath p)) (↑S : Set (Fin m)))
    (i : Fin m) (hi : i ∈ S) : selectedRank p S (step p i) = i.val := by sorry
