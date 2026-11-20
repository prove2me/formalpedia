-- Prove2me | Theorems.Thm_DeletionCode_GoodWordBridge_retainedWords_eq_image_goodVertices
-- name    : DeletionCode.GoodWordBridge.retainedWords_eq_image_goodVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:02:18.833646+00:00
-- url     : https://prove2.me/theorems/281d6c53-30ee-45fd-ba4f-d952e5bf6614
-- title:
--   Good Word Bridge: retained Words eq image good Vertices
-- statement:
--   The graph-to-word projection is the entire retained word set.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GoodWordBridge.lean#L63-L76
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GoodWordBridge.lean#L63-L76

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

theorem DeletionCode.GoodWordBridge.retainedWords_eq_image_goodVertices (t k Q : ℕ)
    (weights : Gram (windowLength k) → ℝ) :
    retainedWords (n := n) t k Q weights =
      (goodVertices (graph (n := n) t Q (realWeightedHash weights))).image Subtype.val := by sorry
