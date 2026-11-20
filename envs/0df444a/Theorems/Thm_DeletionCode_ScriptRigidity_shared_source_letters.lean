-- Prove2me | Theorems.Thm_DeletionCode_ScriptRigidity_shared_source_letters
-- name    : DeletionCode.ScriptRigidity.shared_source_letters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:27.856581+00:00
-- url     : https://prove2.me/theorems/25452e28-90c2-4ce1-a93c-33723437347a
-- title:
--   Script Rigidity: shared source letters
-- statement:
--   Equal long windows after genuine single edits have a common source block
--   at a common window offset. The edits and their source labellings are realized
--   from the original scripts.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ScriptRigidity.lean#L17-L36
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ScriptRigidity.lean#L17-L36

import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_ScriptRigidity
import Theorems.Thm_DeletionCode_EditRigidity_shared_source_letters

set_option autoImplicit true
open DeletionCode DeletionCode.ScriptRigidity
open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.ScriptRigidity.shared_source_letters {k : ℕ} (hk : 1 ≤ k) (x y z : List Bool)
    (hx : KUnique (listLetters x) x.length k)
    (hy : WithinEdits 1 x y) (hz : WithinEdits 1 x z) (a b : ℕ)
    (ha : a + (windowLength k - 1) ≤ y.length)
    (hb : b + (windowLength k - 1) ≤ z.length)
    (hag : Agree (listLetters y) a (listLetters z) b (windowLength k - 1)) :
    ∃ e f : Edit, e.Valid x.length ∧ f.Valid x.length ∧
      e.outputLength x.length = y.length ∧ f.outputLength x.length = z.length ∧
      e.word (listLetters x) = listLetters y ∧ f.word (listLetters x) = listLetters z ∧
      ∃ s r : ℕ, s + k ≤ windowLength k - 1 ∧ r + k ≤ x.length ∧
        ∀ i, i < k →
          e.origin (a + s + i) = some (r + i) ∧
          f.origin (b + s + i) = some (r + i) := by sorry
