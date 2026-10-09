-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgD_bound
-- name    : BookProof.ChapterF6.mgD_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:05:37.192312+00:00
-- url     : https://prove2.me/theorems/dc0c7e99-3b12-4e11-b8c0-4370f236da88
-- title:
--   `BookProof.ChapterF6.mgD_bound` (k : ℕ) (s : List α) : k * mgD k 0 s ≤ s.length
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgD_bound` (k : ℕ) (s : List α) : k * mgD k 0 s ≤ s.length
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgD_bound`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgD_bound
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgD_bound (k : ℕ) (s : List α) : k * mgD k 0 s ≤ s.length := by sorry
