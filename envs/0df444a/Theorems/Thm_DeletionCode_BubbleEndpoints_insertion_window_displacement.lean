-- Prove2me | Theorems.Thm_DeletionCode_BubbleEndpoints_insertion_window_displacement
-- name    : DeletionCode.BubbleEndpoints.insertion_window_displacement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:35:15.536477+00:00
-- url     : https://prove2.me/theorems/046a7790-4dc6-44f0-91a1-7c327a9c41fd
-- title:
--   Bubble Endpoints: insertion window displacement
-- statement:
--   The same displacement follows for an insertion/source pair; the matched
--   letter cannot be the inserted letter, since its origin would be none.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L127-L144
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L127-L144

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubbleEndpoints.insertion_window_displacement {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (pos : ℕ) (bit : Bool) (hpos : pos ≤ n) (s a b : ℕ)
    (ha : s + a + (windowLength k - 1) ≤ n + 1)
    (hb : s + b + (windowLength k - 1) ≤ n)
    (hag : Agree (insertAt x pos bit) (s + a) x (s + b) (windowLength k - 1)) :
    a = b ∨ a = b + 1 := by sorry
