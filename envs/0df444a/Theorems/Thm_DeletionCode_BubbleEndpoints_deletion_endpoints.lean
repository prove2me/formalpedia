-- Prove2me | Theorems.Thm_DeletionCode_BubbleEndpoints_deletion_endpoints
-- name    : DeletionCode.BubbleEndpoints.deletion_endpoints
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:35:28.598318+00:00
-- url     : https://prove2.me/theorems/d1482b38-54b7-450d-a52d-fbcfdbabd54b
-- title:
--   Bubble Endpoints: deletion endpoints
-- statement:
--   Actual local grammar words at the same position in a k-unique source
--   and its deletion share only their initial and terminal vertices.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L172-L189
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L172-L189

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubbleEndpoints.deletion_endpoints {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit))
    (x : Letters) (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n)
    (hslength : s + bubble.shortWord.length ≤ n - 1)
    (hlong : Agree (listLetters bubble.longWord) 0 x s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 (deleteAt x pos) s bubble.shortWord.length)
    (a b : ℕ) (ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.shortWord) b (windowLength k - 1)) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho) := by sorry
