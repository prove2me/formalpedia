-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalProbability_exceptional_iff_candidate
-- name    : DeletionCode.ExceptionalProbability.exceptional_iff_candidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:52.797593+00:00
-- url     : https://prove2.me/theorems/441cd270-9a94-47c9-a8be-fc6bf843c890
-- title:
--   Exceptional Probability: exceptional iff candidate
-- statement:
--   The original exceptional predicate is precisely a label collision with
--   one of these fixed partners, when its source uniqueness condition holds.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L41-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L41-L50

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

theorem DeletionCode.ExceptionalProbability.exceptional_iff_candidate {H : Type*} (t k : ℕ) (label : Bits n → H)
    (x : Bits n) (hx : KUnique (padBits x) n k) :
    FiniteConflictGraph.Exceptional t k label x ↔
      ∃ y ∈ candidatePartners t k x, label x = label y := by sorry
