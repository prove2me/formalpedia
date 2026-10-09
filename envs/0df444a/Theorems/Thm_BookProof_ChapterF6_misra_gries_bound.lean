-- Prove2me | Theorems.Thm_BookProof_ChapterF6_misra_gries_bound
-- name    : BookProof.ChapterF6.misra_gries_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:04:28.210015+00:00
-- url     : https://prove2.me/theorems/e4350392-29a9-4f99-9fa7-80cd63a33a81
-- title:
--   `BookProof.ChapterF6.misra_gries_bound` (k : ℕ) (hk : 1 ≤ k) (s : List α) (x : α) : s.count x - s.length / k ≤ (mg k s) x ∧ (mg k s) x ≤ s.count x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.misra_gries_bound` (k : ℕ) (hk : 1 ≤ k) (s : List α) (x : α) : s.count x - s.length / k ≤ (mg k s) x ∧ (mg k s) x ≤ s.count x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.misra_gries_bound`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.misra_gries_bound
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.misra_gries_bound (k : ℕ) (hk : 1 ≤ k) (s : List α) (x : α) :
    s.count x - s.length / k ≤ (mg k s) x ∧ (mg k s) x ≤ s.count x := by sorry
