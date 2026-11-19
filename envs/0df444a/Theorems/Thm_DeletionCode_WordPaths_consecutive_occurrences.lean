-- Prove2me | Theorems.Thm_DeletionCode_WordPaths_consecutive_occurrences
-- name    : DeletionCode.WordPaths.consecutive_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:58:42.065333+00:00
-- url     : https://prove2.me/theorems/3eb820c7-3bd3-4611-9816-d9866aa5982f
-- title:
--   Word Paths: consecutive occurrences
-- statement:
--   Two consecutive L-windows must occur consecutively in a k-unique x.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordPaths.lean#L21-L36
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordPaths.lean#L21-L36

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_WordPaths
set_option autoImplicit true
open DeletionCode DeletionCode.WordPaths
open Windows

theorem DeletionCode.WordPaths.consecutive_occurrences
    (x p : Letters) (n k L i a b : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hleft : Agree x a p i L) (hright : Agree x b p (i + 1) L) :
    b = a + 1 := by sorry
