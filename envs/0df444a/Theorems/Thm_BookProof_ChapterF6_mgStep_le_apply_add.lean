-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgStep_le_apply_add
-- name    : BookProof.ChapterF6.mgStep_le_apply_add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:02:49.735473+00:00
-- url     : https://prove2.me/theorems/ae615d28-437c-4127-89f0-0a2eca346ed3
-- title:
--   `BookProof.ChapterF6.mgStep_le_apply_add` (k : ℕ) (T : α →₀ ℕ) (x y : α) : T y + (if y = x then 1 else 0) ≤ (mgStep k T x) y + (if 0 < T x ∨ T.support.card < k then 0 else 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgStep_le_apply_add` (k : ℕ) (T : α →₀ ℕ) (x y : α) : T y + (if y = x then 1 else 0) ≤ (mgStep k T x) y + (if 0 < T x ∨ T.support.card < k then 0 else 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgStep_le_apply_add`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgStep_le_apply_add
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgStep_le_apply_add (k : ℕ) (T : α →₀ ℕ) (x y : α) :
    T y + (if y = x then 1 else 0)
      ≤ (mgStep k T x) y + (if 0 < T x ∨ T.support.card < k then 0 else 1) := by sorry
