-- Prove2me | Theorems.Thm_DeletionCode_WordPaths_all_windows_occur_implies_subword
-- name    : DeletionCode.WordPaths.all_windows_occur_implies_subword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:58:42.748515+00:00
-- url     : https://prove2.me/theorems/3faf6213-1b5f-4304-9eaf-4f9b252294e2
-- title:
--   Word Paths: all windows occur implies subword
-- statement:
--   All L-windows of p occurring in x forces the whole length-(L+D) word to
--   occur in x. This establishes contiguity rather than taking it as a premise.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordPaths.lean#L42-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordPaths.lean#L42-L80

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_WordPaths
set_option autoImplicit true
open DeletionCode DeletionCode.WordPaths
open Windows

theorem DeletionCode.WordPaths.all_windows_occur_implies_subword
    (x p : Letters) (n k L D : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (hocc : ∀ i, i ≤ D → Occurs x n p i L) :
    ∃ a, a + (L + D) ≤ n ∧ Agree x a p 0 (L + D) := by sorry
