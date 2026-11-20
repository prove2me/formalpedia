-- Prove2me | Theorems.Thm_DeletionCode_BubbleEndpoints_deletion_window_displacement
-- name    : DeletionCode.BubbleEndpoints.deletion_window_displacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:17.324786+00:00
-- url     : https://prove2.me/theorems/32ff6dcc-0563-434a-aecb-54b6adcc1b63
-- title:
--   Bubble Endpoints: deletion window displacement
-- statement:
--   A shared source letter in a source/deletion pair fixes the offset displacement.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L108-L123
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L108-L123

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubbleEndpoints.deletion_window_displacement {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s a b : ℕ)
    (ha : s + a + (windowLength k - 1) ≤ n)
    (hb : s + b + (windowLength k - 1) ≤ n - 1)
    (hag : Agree x (s + a) (deleteAt x pos) (s + b) (windowLength k - 1)) :
    a = b ∨ a = b + 1 := by sorry
