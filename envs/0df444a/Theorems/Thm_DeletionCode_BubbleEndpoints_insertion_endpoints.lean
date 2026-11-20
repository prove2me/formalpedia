-- Prove2me | Theorems.Thm_DeletionCode_BubbleEndpoints_insertion_endpoints
-- name    : DeletionCode.BubbleEndpoints.insertion_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:47.844822+00:00
-- url     : https://prove2.me/theorems/ec3c31ae-497e-4d44-8516-f6b621bc0bdd
-- title:
--   Bubble Endpoints: insertion endpoints
-- statement:
--   The corresponding result when the shorter grammar word lies in the
--   source and the longer word lies at the same position after an insertion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L193-L210
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L193-L210

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubbleEndpoints.insertion_endpoints {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit))
    (x : Letters) (hx : KUnique x n k) (pos : ℕ) (bit : Bool) (hpos : pos ≤ n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n + 1)
    (hslength : s + bubble.shortWord.length ≤ n)
    (hlong : Agree (listLetters bubble.longWord) 0 (insertAt x pos bit) s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 x s bubble.shortWord.length)
    (a b : ℕ) (ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.shortWord) b (windowLength k - 1)) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho) := by sorry
