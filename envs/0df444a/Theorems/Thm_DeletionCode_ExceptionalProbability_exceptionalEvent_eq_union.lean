-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalProbability_exceptionalEvent_eq_union
-- name    : DeletionCode.ExceptionalProbability.exceptionalEvent_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:55.972841+00:00
-- url     : https://prove2.me/theorems/659ba9f5-8b53-4fd9-9b67-ccb6cc5229fc
-- title:
--   Exceptional Probability: exceptional Event eq union
-- statement:
--   The Exceptional Probability construction uses the exceptional Event eq union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L98-L104
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L98-L104

import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_ExceptionalProbability
set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform
open ConflictGraphWitness
open scoped BigOperators
variable {n : ℕ}

theorem DeletionCode.ExceptionalProbability.exceptionalEvent_eq_union (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) :
    exceptionalEvent t k Q x = ⋃ y ∈ candidatePartners t k x, collisionEvent k Q x y := by sorry
