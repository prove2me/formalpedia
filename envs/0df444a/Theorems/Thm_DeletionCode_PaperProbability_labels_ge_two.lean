-- Prove2me | Theorems.Thm_DeletionCode_PaperProbability_labels_ge_two
-- name    : DeletionCode.PaperProbability.labels_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:05:10.081785+00:00
-- url     : https://prove2.me/theorems/fd8e73d5-94bb-48e1-b515-20fdc8f73d35
-- title:
--   Paper Probability: labels ge two
-- statement:
--   The Paper Probability construction uses the labels ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean#L18-L25
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean#L18-L25

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_PaperProbability
set_option autoImplicit true
open DeletionCode DeletionCode.PaperProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal

theorem DeletionCode.PaperProbability.labels_ge_two (t n Q : ℕ) (hn : 1 ≤ n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) : 2 ≤ Q := by sorry
