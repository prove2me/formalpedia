-- Prove2me | Theorems.Thm_DeletionCode_PaperProbability_total_discard_le
-- name    : DeletionCode.PaperProbability.total_discard_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:04:47.158886+00:00
-- url     : https://prove2.me/theorems/9e1b776a-2928-40f8-b08f-e2d23bcf7d3d
-- title:
--   Paper Probability: total discard le
-- statement:
--   The Paper Probability construction uses the total discard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean#L54-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean#L54-L74

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_PaperProbability
import Theorems.Thm_DeletionCode_PaperParameters_threshold

set_option autoImplicit true
open DeletionCode DeletionCode.PaperProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal

theorem DeletionCode.PaperProbability.total_discard_le {n : ℕ} (t Q : ℕ) (ht : 2 ≤ t) (x : Bits n)
    (hx : KUnique (padBits x) n (PaperParameters.k n))
    (hfit : PaperParameters.L n ≤ n) (hready : threshold t ≤ PaperParameters.L n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) :
    realWeights (Gram (PaperParameters.L n))
      (exceptionalEvent t (PaperParameters.k n) Q x ∪ obstructionEvent t (PaperParameters.k n) Q x) ≤
        ENNReal.ofReal (1 / 3 : ℝ) := by sorry
