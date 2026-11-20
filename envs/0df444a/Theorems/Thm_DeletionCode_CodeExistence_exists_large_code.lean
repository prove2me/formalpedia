-- Prove2me | Theorems.Thm_DeletionCode_CodeExistence_exists_large_code
-- name    : DeletionCode.CodeExistence.exists_large_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:09:00.955834+00:00
-- url     : https://prove2.me/theorems/6e0ef098-d457-4e7f-8b3c-5397b2faff2c
-- title:
--   Code Existence: exists large code
-- statement:
--   The finite code-size bound under the explicit parameter thresholds.
--   The code corrects the actual insertion/deletion relation on binary words.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean#L28-L67
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean#L28-L67

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
import Definitions.Def_DeletionCode_CodeExistence
import Theorems.Thm_DeletionCode_PaperParameters_threshold

set_option autoImplicit true
open DeletionCode DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection

theorem DeletionCode.CodeExistence.exists_large_code (t n : ℕ) (ht : 2 ≤ t) (hn : 1 ≤ n)
    (hfit : PaperParameters.L n ≤ n)
    (hready : PaperProbability.threshold t ≤ PaperParameters.L n) :
    ∃ C : Finset (Bits n), Corrects t C ∧
      2 ^ n ≤ 8 * RedundancyBounds.labelCount t n * C.card := by sorry
