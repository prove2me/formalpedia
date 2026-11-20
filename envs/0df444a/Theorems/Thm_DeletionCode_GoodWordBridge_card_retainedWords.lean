-- Prove2me | Theorems.Thm_DeletionCode_GoodWordBridge_card_retainedWords
-- name    : DeletionCode.GoodWordBridge.card_retainedWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:02:20.892673+00:00
-- url     : https://prove2.me/theorems/596abd04-508f-4118-9fd6-f44e739b0ad3
-- title:
--   Good Word Bridge: card retained Words
-- statement:
--   Actual retained words and actual good graph vertices have the same cardinality.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GoodWordBridge.lean#L79-L86
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GoodWordBridge.lean#L79-L86

import Definitions.Def_DeletionCode_CodeSelection
import Definitions.Def_DeletionCode_UniqueWordCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_GoodWordBridge
set_option autoImplicit true
open DeletionCode DeletionCode.GoodWordBridge
open Windows HeaderRecovery SignedSupport CircleHash ConflictGraphWitness
open ExceptionalProbability ObstructionProbability BipartiteSelection
variable {n : ℕ}

theorem DeletionCode.GoodWordBridge.card_retainedWords (t k Q : ℕ) (weights : Gram (windowLength k) → ℝ) :
    (retainedWords (n := n) t k Q weights).card =
      (goodVertices (graph (n := n) t Q (realWeightedHash weights))).card := by sorry
