-- Prove2me | Theorems.Thm_DeletionCode_WordPaths_subword_position_unique
-- name    : DeletionCode.WordPaths.subword_position_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:58:44.236705+00:00
-- url     : https://prove2.me/theorems/c902ab3c-db3a-4d37-ad20-c67b9dce9b4a
-- title:
--   Word Paths: subword position unique
-- statement:
--   The full word occurrence is unique; no second root position is needed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordPaths.lean#L83-L91
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordPaths.lean#L83-L91

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_WordPaths
set_option autoImplicit true
open DeletionCode DeletionCode.WordPaths
open Windows

theorem DeletionCode.WordPaths.subword_position_unique
    (x p : Letters) (n k m a b : ℕ)
    (hx : KUnique x n k) (hkm : k ≤ m)
    (ha : a + m ≤ n) (hb : b + m ≤ n)
    (hleft : Agree x a p 0 m) (hright : Agree x b p 0 m) :
    a = b := by sorry
