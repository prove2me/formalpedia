-- Prove2me | Theorems.Thm_DeletionCode_PaperProbability_exceptional_quarter_bound
-- name    : DeletionCode.PaperProbability.exceptional_quarter_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:04:26.412506+00:00
-- url     : https://prove2.me/theorems/fa748c6c-2b74-428b-88d3-41e96e318788
-- title:
--   Paper Probability: exceptional quarter bound
-- statement:
--   The Paper Probability construction uses the exceptional quarter bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean#L27-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean#L27-L52

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_PaperProbability
set_option autoImplicit true
open DeletionCode DeletionCode.PaperProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal

theorem DeletionCode.PaperProbability.exceptional_quarter_bound {n : ℕ} (t Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n (PaperParameters.k n))
    (hfit : PaperParameters.L n ≤ n)
    (hconstant : exceptionalConstant t ≤ PaperParameters.L n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) :
    realWeights (Gram (PaperParameters.L n))
        (exceptionalEvent t (PaperParameters.k n) Q x) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by sorry
