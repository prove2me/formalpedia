-- Prove2me | Theorems.Thm_DeletionCode_CodeExistence_main
-- name    : DeletionCode.CodeExistence.main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:08:57.820385+00:00
-- url     : https://prove2.me/theorems/e39a0eb2-bff1-4b06-ba1c-0ff11660b112
-- title:
--   Code Existence: main
-- statement:
--   The code-existence form of the manuscript's main theorem, with the
--   O_t(log log n) term expressed by an explicit existential constant.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean#L87-L96
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean#L87-L96

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
import Definitions.Def_DeletionCode_CodeExistence
set_option autoImplicit true
open DeletionCode DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection

theorem DeletionCode.CodeExistence.main (t : ℕ) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (Bits n),
      Corrects t C ∧ C.Nonempty ∧
      RedundancyBounds.redundancy n C ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          (K : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) := by sorry
