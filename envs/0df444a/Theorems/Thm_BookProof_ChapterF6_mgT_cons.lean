-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgT_cons
-- name    : BookProof.ChapterF6.mgT_cons
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:02:07.941299+00:00
-- url     : https://prove2.me/theorems/f5d799b8-0765-469e-b6d9-06dbfef99947
-- title:
--   `BookProof.ChapterF6.mgT_cons` (k : ℕ) (T : α →₀ ℕ) (x : α) (xs : List α) : mgT k T (x :: xs) = mgT k (mgStep k T x) xs
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgT_cons` (k : ℕ) (T : α →₀ ℕ) (x : α) (xs : List α) : mgT k T (x :: xs) = mgT k (mgStep k T x) xs
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgT_cons`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgT_cons
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgT_cons (k : ℕ) (T : α →₀ ℕ) (x : α) (xs : List α) :
    mgT k T (x :: xs) = mgT k (mgStep k T x) xs := by sorry
