-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgT_sum_add
-- name    : BookProof.ChapterF6.mgT_sum_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:04:09.6279+00:00
-- url     : https://prove2.me/theorems/5c9bf36e-9c51-4ef1-a1d4-29a31c52bc1e
-- title:
--   `BookProof.ChapterF6.mgT_sum_add` (k : ℕ) (T : α →₀ ℕ) (s : List α) (hT : T.support.card ≤ k) : mgSum (mgT k T s) + (k + 1) * mgD k T s = mgSum T + s.length
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgT_sum_add` (k : ℕ) (T : α →₀ ℕ) (s : List α) (hT : T.support.card ≤ k) : mgSum (mgT k T s) + (k + 1) * mgD k T s = mgSum T + s.length
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgT_sum_add`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgT_sum_add
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgT_sum_add (k : ℕ) (T : α →₀ ℕ) (s : List α) (hT : T.support.card ≤ k) :
    mgSum (mgT k T s) + (k + 1) * mgD k T s = mgSum T + s.length := by sorry
