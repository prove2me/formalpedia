-- Prove2me | Theorems.Thm_DeletionCode_GoodWordBridge_mem_retainedWords_iff
-- name    : DeletionCode.GoodWordBridge.mem_retainedWords_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:02:34.242175+00:00
-- url     : https://prove2.me/theorems/5e00f739-5abb-4404-a45d-5ae5a80d0ac2
-- title:
--   Good Word Bridge: mem retained Words iff
-- statement:
--   The probabilistic tests retain exactly the underlying words of vertices
--   whose actual connected components are two-colorable.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GoodWordBridge.lean#L28-L60
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GoodWordBridge.lean#L28-L60

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

theorem DeletionCode.GoodWordBridge.mem_retainedWords_iff (t k Q : ℕ) (weights : Gram (windowLength k) → ℝ)
    (x : Bits n) :
    x ∈ retainedWords t k Q weights ↔
      ∃ v : Vertex (n := n) t Q (realWeightedHash weights), v.val = x ∧
        Good (graph t Q (realWeightedHash weights)) v := by sorry
