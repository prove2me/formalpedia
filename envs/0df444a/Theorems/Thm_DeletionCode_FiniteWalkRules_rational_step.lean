-- Prove2me | Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
-- name    : DeletionCode.FiniteWalkRules.rational_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:02.007195+00:00
-- url     : https://prove2.me/theorems/d5c439ab-4652-4ac9-8447-aeb0fad542bf
-- title:
--   Finite Walk Rules: rational step
-- statement:
--   The Finite Walk Rules construction uses the rational step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L30-L34
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteWalkRules.lean#L30-L34

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}

theorem DeletionCode.FiniteWalkRules.rational_step
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (i : Fin m) :
    rational (step p i) = walkStep (rationalPath p) i := by sorry
