-- Prove2me | Theorems.Thm_DeletionCode_CodeExistence_eventually_exists_code
-- name    : DeletionCode.CodeExistence.eventually_exists_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:09:25.787637+00:00
-- url     : https://prove2.me/theorems/f2b3b47c-104b-43b8-a1e5-980da05d2c01
-- title:
--   Code Existence: eventually exists code
-- statement:
--   For every fixed t ≥ 2 and all sufficiently large n, an actual binary
--   code corrects t insertions/deletions and has the stated explicit redundancy.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean#L71-L83
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean#L71-L83

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
import Definitions.Def_DeletionCode_CodeExistence
set_option autoImplicit true
open DeletionCode DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection

theorem DeletionCode.CodeExistence.eventually_exists_code (t : ℕ) (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits n),
      Corrects t C ∧ C.Nonempty ∧
      2 ^ n ≤ 8 * RedundancyBounds.labelCount t n * C.card ∧
      RedundancyBounds.redundancy n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          ((6 * WitnessCost.exponent t + 6 : ℕ) : ℝ) *
            Real.logb 2 (Real.logb 2 (n : ℝ)) := by sorry
