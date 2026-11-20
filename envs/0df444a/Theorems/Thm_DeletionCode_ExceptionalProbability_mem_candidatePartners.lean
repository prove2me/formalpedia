-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalProbability_mem_candidatePartners
-- name    : DeletionCode.ExceptionalProbability.mem_candidatePartners
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:53.324515+00:00
-- url     : https://prove2.me/theorems/449629db-9115-4442-8469-7b31e719a970
-- title:
--   Exceptional Probability: mem candidate Partners
-- statement:
--   The Exceptional Probability construction uses the mem candidate Partners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L34-L37
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L34-L37

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

theorem DeletionCode.ExceptionalProbability.mem_candidatePartners (t k : ℕ) (x y : Bits n) :
    y ∈ candidatePartners t k x ↔ CandidatePartner t k x y := by sorry
