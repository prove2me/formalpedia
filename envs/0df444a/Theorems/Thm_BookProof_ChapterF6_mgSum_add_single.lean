-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgSum_add_single
-- name    : BookProof.ChapterF6.mgSum_add_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:03:33.899013+00:00
-- url     : https://prove2.me/theorems/446360f1-d62d-42f1-9c61-c51ec6202eb4
-- title:
--   `BookProof.ChapterF6.mgSum_add_single` (T : α →₀ ℕ) (x : α) : mgSum (T + Finsupp.single x 1) = mgSum T + 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgSum_add_single` (T : α →₀ ℕ) (x : α) : mgSum (T + Finsupp.single x 1) = mgSum T + 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgSum_add_single`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgSum_add_single
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgSum_add_single (T : α →₀ ℕ) (x : α) :
    mgSum (T + Finsupp.single x 1) = mgSum T + 1 := by sorry
