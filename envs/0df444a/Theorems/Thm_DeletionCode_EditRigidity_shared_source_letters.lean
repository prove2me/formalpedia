-- Prove2me | Theorems.Thm_DeletionCode_EditRigidity_shared_source_letters
-- name    : DeletionCode.EditRigidity.shared_source_letters
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:19:44.973903+00:00
-- url     : https://prove2.me/theorems/6dbb264c-6388-4dac-a6a9-203105976ce6
-- title:
--   Edit Rigidity: shared source letters
-- statement:
--   The shared-source-letters assertion in manuscript lemma `lem:rigidity`.
--   The edits and all surviving source indices are actual data. Positivity of k
--   is explicit; the manuscript fixes k = 2*ceil(log₂ n)+2.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditRigidity.lean#L19-L47
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditRigidity.lean#L19-L47

import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_TwoEditWindows
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_EditRigidity
set_option autoImplicit true
open DeletionCode DeletionCode.EditRigidity
open Windows HeaderRecovery SingleEditOrigins

theorem DeletionCode.EditRigidity.shared_source_letters {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (a b : ℕ) (ha : a + (windowLength k - 1) ≤ e.outputLength n)
    (hb : b + (windowLength k - 1) ≤ f.outputLength n)
    (hag : Agree (e.word x) a (f.word x) b (windowLength k - 1)) :
    ∃ s r : ℕ, s + k ≤ windowLength k - 1 ∧ r + k ≤ n ∧
      ∀ i, i < k →
        e.origin (a + s + i) = some (r + i) ∧
        f.origin (b + s + i) = some (r + i) := by sorry
