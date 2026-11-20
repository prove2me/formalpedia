-- Prove2me | Theorems.Thm_DeletionCode_NonseparatedFamily_exceptional_measure_le
-- name    : DeletionCode.NonseparatedFamily.exceptional_measure_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:40.458249+00:00
-- url     : https://prove2.me/theorems/18165cb2-8156-4d6d-8646-7fc2899bbe2f
-- title:
--   Nonseparated Family: exceptional measure le
-- statement:
--   The Nonseparated Family construction uses the exceptional measure le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/NonseparatedFamily.lean#L13-L23
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/NonseparatedFamily.lean#L13-L23

import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Definitions.Def_DeletionCode_NonseparatedFamily
set_option autoImplicit true
open DeletionCode DeletionCode.NonseparatedFamily
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform ConflictGraphWitness
open ExceptionalProbability ExceptionalPartnerCount ExceptionalCountArithmetic

theorem DeletionCode.NonseparatedFamily.exceptional_measure_le {n : ℕ} (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    realWeights (Gram (windowLength k)) (exceptionalEvent t k Q x) ≤
      (exceptionalConstant t * windowLength k * n ^ (2 * t - 1) : ℕ) *
        ENNReal.ofReal (2 / (Q : ℝ)) := by sorry
