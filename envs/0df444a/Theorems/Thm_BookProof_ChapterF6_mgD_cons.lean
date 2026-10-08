-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgD_cons
-- name    : BookProof.ChapterF6.mgD_cons
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:01:56.147544+00:00
-- url     : https://prove2.me/theorems/042ad495-d912-47b1-b2cd-0d3cab5d51c6
-- title:
--   `BookProof.ChapterF6.mgD_cons` (k : ℕ) (T : α →₀ ℕ) (x : α) (xs : List α) : mgD k T (x :: xs) = (if 0 < T x ∨ T.support.card < k then 0 else 1) + mgD k (mgStep k T x) xs
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgD_cons` (k : ℕ) (T : α →₀ ℕ) (x : α) (xs : List α) : mgD k T (x :: xs) = (if 0 < T x ∨ T.support.card < k then 0 else 1) + mgD k (mgStep k T x) xs
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgD_cons`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgD_cons
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgD_cons (k : ℕ) (T : α →₀ ℕ) (x : α) (xs : List α) :
    mgD k T (x :: xs) =
      (if 0 < T x ∨ T.support.card < k then 0 else 1) + mgD k (mgStep k T x) xs := by sorry
