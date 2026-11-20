-- Prove2me | Theorems.Thm_DeletionCode_NonseparatedFamily_exceptional_probability_bound
-- name    : DeletionCode.NonseparatedFamily.exceptional_probability_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:46.776616+00:00
-- url     : https://prove2.me/theorems/424931fe-5769-4701-b002-9be806b4faee
-- title:
--   Nonseparated Family: exceptional probability bound
-- statement:
--   Ordinary-real probability form, with an explicit constant depending only on t.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/NonseparatedFamily.lean#L26-L39
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/NonseparatedFamily.lean#L26-L39

import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Definitions.Def_DeletionCode_NonseparatedFamily
set_option autoImplicit true
open DeletionCode DeletionCode.NonseparatedFamily
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform ConflictGraphWitness
open ExceptionalProbability ExceptionalPartnerCount ExceptionalCountArithmetic

theorem DeletionCode.NonseparatedFamily.exceptional_probability_bound {n : ℕ} (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    (realWeights (Gram (windowLength k)) (exceptionalEvent t k Q x)).toReal ≤
      2 * (exceptionalConstant t : ℝ) * (n : ℝ) ^ (2 * t - 1) * (windowLength k : ℝ) / Q := by sorry
